(* Runs the subroutines of the binary program in Unicorn.

   The machine state stays in Primus, Unicorn borrows it while it runs:

   - the registers are written to Unicorn before it starts, the changed
     ones are read back when it stops, and the ones that Primus writes
     meanwhile are written to Unicorn before it continues;

   - the memory pages are copied from Primus when Unicorn faults on
     them, the changed bytes of the pages, that the code wrote, are
     copied back when Primus accesses them, see [Primus.Memory.Backing],
     and the bytes that Primus stores are copied to Unicorn;

   - the code that Primus links instead of the program, e.g., the Lisp
     stubs, stops Unicorn at its address and is called by the Primus
     linker, after which Unicorn continues from the return address,
     except the functions of libc that run on the state of Unicorn,
     e.g., memcpy, see [Primus_native_libc], which don't copy it to
     Primus.

   A run ends when the subroutine returns, i.e., when the code reaches
   its return address with the stack pointer of the caller.

   A checkpoint of the machine is saved when Unicorn reaches its address
   for the first time, and a machine that restores it continues from
   there, instead of the first subroutine that it runs, e.g., the entry
   point, see [Primus_native_checkpoint]. *)

open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
module Uc = Bap_engine
module Target = Primus_native_target
module Checkpoint = Primus_native_checkpoint

(* the seconds of the monotonic clock, which measures the time slices of
   the threads, and the time, that the machines run, see [Make.account],
   and which the timeouts of the engines are of, rather than the processor
   time, of Sys.time, which the engines don't measure, which would make
   the slices and the timeouts take more and more time, while the system
   is loaded, and whose steps are 15.6 ms on Windows, longer than a slice *)
let clock () = Mtime.Span.to_float_ns (Mtime_clock.elapsed ()) *. 1e-9

module Native = Primus_native_libc
include Bap_main.Loggers ()

type Primus.exn += Unicorn_failure of string

let () =
  Primus.Exn.add_printer (function
    | Unicorn_failure msg -> Some ("Unicorn: " ^ msg)
    | _ -> None)

exception Unsupported of string

let page_size = 0x1000L
let page_of addr = Int64.(addr land lnot (page_size - 1L))

type reason =
  | Returned
  | Foreign of int64
  | Fault of Uc.access * int64
  | Interrupt of int  (** an interrupt or a system call *)
  | Invalid
  | Checkpoint
  | Stop of int64  (** a stop of Primus, see [Primus.Interpreter.Stops] *)
  | Pause  (** the script, that drives the machine, asks it to pause *)
  | Jump of int64  (** a call hook returned, see [call_hooks] *)
  | Observe of int64
      (** the observers see the events of the code before the address, see
          [watch] *)
  | Interpret of int64
      (** the instruction at the address uses a tracked register, see [trace] *)
  | Unknown of int64
      (** the registers of the instruction at the address are not known yet, see
          [trace] *)
  | Interrupted
      (** a signal stopped Unicorn, so that its handler runs, see [start_uc] *)

(* a pending return of a run *)
type frame = { ret : int64; sp : int64 }

(* the copied page, with the contents of a writable page that Primus
   has, and the ranges of the bytes that Primus did not have, which it
   may allocate later, so the page is dropped, if it does. A writable
   page is read-only in Unicorn, until the code writes it, which makes
   it dirty and writable, see [written_page], so that only the dirty
   pages are copied back. A dirty page is pending, see [Make.pending],
   until Primus fetches it, which makes it clean again, if it didn't
   change, so that a dirty page stays writable, while the code changes
   it, as changing the protection costs more than comparing the page,
   e.g., of the stack *)
type page = {
  snapshot : Bytes.t option;
  holes : (int * int) list;
  perm : Uc.Perm.t;  (** the access to the page in Primus *)
  mutable dirty : bool;
  mutable fetched : int;  (** the run of Unicorn, after which it is fetched *)
}

(* the page of a machine, that doesn't run in Unicorn, with the
   contents that it had in Unicorn, which go there again, when the
   machine runs in Unicorn, unless Primus drops the page meanwhile, see
   [Make.protected]. The page is pending, until Primus fetches it *)
type parked = { data : Bytes.t; copy : page; mutable unfetched : bool }

(* the registers of the basis, that the instruction reads, and the ones
   that it writes whole, unless it writes them conditionally *)
type access = {
  uses : string list;
  defs : string list;
  memory : bool;
  code : string;  (** the bytes of the instruction *)
}

(* the call of a native function: the expressions of its arguments and
   of its result, which are registers, their parts, or the words on
   the stack, see [Make.eval_uc] *)
type native = { fn : Native.fn; args : exp list; result : (exp * int) option }

(* the arguments and the result of a function, see [native] *)
type signature = { inputs : exp list; output : (exp * int) option }

(* what a hook of a call does: the function runs, or returns the value
   at once *)
type action = Default | Return of int64

(* the loads and the stores of the code, that the observers see, after
   its instruction runs, with their addresses, sizes and values *)
type event = Loaded of int64 * int * int64 | Stored of int64 * int * int64

module Id = Monads.Std.Monad.State.Multi.Id

(* the engines of the executors, bap:unicorn-executor, and
   bap:lifted-executor, see [Bap_lifted] *)
type kind = [ `Unicorn | `Lifted ]

(* the options of the plugin of an engine, primus-unicorn, or
   primus-lifted, which are the defaults of its sessions: the seconds that
   a machine may run, the file of the checkpoint and its point, the file
   of the checkpoint to continue from, the functions of libc that run
   natively, and if the lifted engine compiles its blocks *)
type options = {
  mutable timeout : float option;
  mutable checkpoint : (string * string) option;
  mutable restore : string option;
  mutable native_stubs : String.Set.t;
  mutable jit : bool;
  mutable cache : string option;
      (** the folder of the caches of the lifted engine, of its compiled blocks,
          and of its lifted instructions, see [lifter] *)
  mutable digest : string;
      (** the digest of the version of BAP, and of the configuration of its
          plugins, that lift the instructions, see [lifter] *)
}

type engine = {
  session : session;  (** the system, whose machines run in the engine *)
  uc : Uc.t;
  arch : Uc.arch;
  regs : Target.Regs.t;
  pc : int;
  sp : var;
  link : var option;
  bytes : int;  (** the size of an address *)
  basis : var list;  (** the mapped registers that are not aliases *)
  pages : page Int64.Table.t;
  trampolines : string Int64.Table.t;
      (** the addresses that stand for the external functions *)
  slots : (int * int64) list Int64.Table.t;
      (** the offsets in the pages of the slots, e.g., of GOT, which refer to
          the external functions, and their trampolines *)
  big_endian : bool;
  r6 : bool;
      (** the release 6 of MIPS, whose compact branches have no delay slots *)
  mutable owner : Primus.Machine.id option;
  mutable reason : reason option;
  mutable frames : frame list;
      (** the pending returns of the machine that runs, see [frames] *)
  returns : unit Int64.Table.t;
      (** the addresses of the hooks of the returns, which stay, as the
          addresses are few *)
  synced : word String.Table.t;
      (** the values of the registers that Primus and Unicorn agree on *)
  mutable unchecked : (int64 * (int * int) list) list;
      (** the pages with holes, which Primus may have allocated *)
  mutable dirty : int64 list;  (** the dirty pages *)
  mutable runs : int;  (** the number of the runs of Unicorn *)
  mutable written : var list;
      (** the registers that Primus has written since Unicorn stopped *)
  mutable broken : bool;
      (** Unicorn 2.1.4 crashes on MIPS after a fetch fault, so the engine is
          created anew *)
  hooked : Int64.Hash_set.t;
      (** the addresses of the checkpoint and of the stops, which have the hook,
          see [dispatch] *)
  mutable stops : int;  (** the version of the stops, which are hooked *)
  mutable stepper : Uc.hook option;
      (** the hook of every address, while the stepping is on *)
  mutable watching : watching;  (** the events that the observers see *)
  mutable code_segments : (int64 * int64) list;
      (** the executable segments of the program, whose writes are watched, see
          [watching], as the dynamic code of Primus sees them *)
  code_written : (int64 * int64) list Int64.Table.t;
      (** the ranges of the addresses of the code, that the program wrote, since
          the engine stopped, by their pages, merged, see [code_written] *)
  mutable watchers : Uc.hook list;  (** the hooks of the events *)
  mutable observed : (int64 * int) option;
      (** the address of the last observation and the start of Unicorn *)
  accesses : access Int64.Table.t;  (** the accesses of the instructions *)
  foreign : Int64.Hash_set.t;
      (** the addresses of the code, that Primus runs instead *)
  tracked : String.Hash_set.t;
      (** the registers of the basis, whose values Primus tracks, see
          [Primus.Track] *)
  mutable clobbered : string list;
      (** the tracked registers, that the code in Unicorn wrote *)
  mutable tracer : Uc.hook option;
      (** the hook of every address, while a register is tracked *)
  mutable seen : int;  (** the version of [Primus.Track], that is seen *)
  mutable shadowing : bool;
      (** if the lifted engine propagates the taint, see [Make.Shadow] *)
  mutable shadowed : bool;
      (** if the engine has the taint of the memory, so that it gets only its
          changes, see [Make.Shadow.import] *)
  known : Primus.value Int.Table.t;
      (** the objects of the labels, that the engine has seen, whose classes it
          has, see [Make.Shadow.import] *)
}

(* the events of the code, that the observers of the machine see, which
   are hooked, only when they are observed, see [Make.watching] *)
and watching = {
  pcs : bool;
  reads : bool;
  writes : bool;
  code_writes : bool;
      (** the writes to the code of the program only, see [code_segments], if
          not all of the writes, see [Primus.Track.cover_code] *)
}

(* The state of a system, whose machines run in Unicorn, which is of the
   system, see [session_state], as the systems, e.g., the emulators of a
   script, see [Bap_emu], run in the same process, each with its own
   engine. *)
(* the lifter of the lifted engine, see [lifter] *)
and lifter = {
  lift : thumb:bool -> int64 -> string -> (int * string * blk term list) option;
      (** lifts the instruction at the address, in the mode, from its bytes *)
  name : tid -> string option;
      (** the name of the label, that the instruction calls, e.g., of an
          intrinsic *)
  cached : bool;  (** if the cache had the instructions *)
  save : unit -> unit;
      (** saves the instructions to the cache, if it has one, and they changed,
          as the run does, when it exits *)
}

and session = {
  mutable active : engine option;  (** the engine of the machines *)
  mutable recipe :
    (Theory.Target.t * int64 list * (int64 * string) list) option;
      (** the arguments of [create] *)
  parked : parked Int64.Table.t Id.Table.t;
      (** the pages of the machines, that don't run in Unicorn, see [Make.park]
      *)
  mutable parked_pages : int;  (** the number of the parked pages *)
  dead : Id.Hash_set.t;  (** the killed machines, whose pages are not parked *)
  own_code : Primus.Linker.code Addr.Table.t;
      (** the code that runs the subroutines in Unicorn, see [Loader] *)
  stubs : Primus.Linker.code Addr.Table.t;
      (** the stubs of the external functions, e.g., in PLT, which jump through
          their slots to the trampolines, interpreted, see [call_foreign] *)
  native_stubs : String.Set.t;  (** the functions of libc that run natively *)
  natives : native String.Table.t;
      (** the native functions that the program calls, by their names *)
  signatures : signature String.Table.t;
      (** the signatures of the functions of the program, by their names *)
  names : string Int64.Table.t;
      (** the names of the subroutines of the program, by their addresses *)
  symbols : string Int64.Table.t;
      (** the names of the code, that the script gave, e.g., of the code, that
          the program unpacked, see [Bap_emu.add_symbol], which the checkpoints
          keep, as the program doesn't have them *)
  unstubbed : Int64.Hash_set.t;
      (** the functions of the program, whose code runs in Unicorn, instead of
          the stubs, that replaced them, e.g., in Lisp, see [Bap_emu.unstub],
          which the checkpoints keep *)
  thumb : Addr.Hash_set.t;
      (** the subroutines in the Thumb encoding, which Unicorn runs from their
          addresses with the lower bit set *)
  thumb_symbols : Int64.Hash_set.t;
      (** the addresses of the symbols in the Thumb encoding, whose values have
          the lower bit set, which tell the encoding of the subroutines without
          the code, e.g., of the bare project *)
  mutable bare_mode : bool;
      (** the machine runs without the disassembled program, which the bare
          project does not have, see [Bap_script.project] *)
  timeout : float option;
      (** the seconds that a machine may run, in Unicorn and in Primus, e.g., in
          the Lisp stubs *)
  mutable accounted : float;
      (** the time of [clock], which the machines have accounted for, see
          [account] *)
  mutable ticks : int;
      (** the clock ticks of Primus since the time was last checked, see
          [clocked] *)
  checkpoint : (string * string) option;
      (** the file of the checkpoint and the address or the name of the
          subroutine, at which it is saved *)
  mutable checkpoint_addr : int64 option;  (** the address of the checkpoint *)
  mutable checkpointed : bool;  (** the checkpoint is saved once *)
  restore : string option;
      (** the file of the checkpoint, from which the machines continue *)
  mutable restored_from : Checkpoint.t option;
  mutable resumed_at : int64 option;
      (** the machine doesn't stop at the address, from which it continues,
          e.g., after a stop or a checkpoint, until its instruction runs, which
          it does, unless it faults, after the hook has skipped the address, see
          [skipped_at] *)
  mutable skipped_at : int64 option;
  mutable stops_seen : int;
      (** the version of the stops of the system, see
          [Primus.Interpreter.Stops], whose copy the hooks see *)
  mutable stepping : bool;
  stop_addrs : Int64.Hash_set.t;
  lifted : bool;
      (** the machines run in the lifted engine, see [Bap_lifted], of
          bap:lifted-executor, rather than in Unicorn *)
  jit : bool;  (** the lifted engine compiles the blocks, that run often *)
  cache : string option;  (** see [options.cache] *)
  digest : string;  (** see [options.digest] *)
  mutable lifter : lifter option;
      (** lifts the instructions for the lifted engine, see [lifter] *)
  mutable driven : bool;
      (** the script drives the machines, see [Bap_emu], which pause, when
          [pause] is set *)
  mutable pause : bool;
  mutable saved : (unit, string) result;  (** the result of the last [Save] *)
  mutable spawned : (int, string) result;  (** the result of the last [Spawn] *)
  mutable starts : int;
      (** the number of the starts of Unicorn, which tells the instruction that
          runs again, e.g., after its fault, from the next one *)
  mutable stopped_at : int64 option;
      (** the address of the code, at which Unicorn stopped last, before it ran
          the instruction there, whose hooks may have run, e.g., when they
          stopped it *)
  mutable restarted_at : int64 option;
      (** the address of the code, at which Unicorn starts again, after it
          stopped there, so that the hooks of the instruction, which ran in the
          previous start, run again, e.g., of the calls, see [Bap_emu.on_call]
      *)
  call_hooks : (unit -> action) list String.Table.t;
      (** the hooks of the calls of the functions, by their names, the latest
          first *)
  mutable exit_code : int option;
      (** the code, with which the program exited *)
  mutable engine_hooks : (engine -> unit) list;
      (** the hooks of the script, which every new engine gets, as the engine
          may be created anew, see [broken] *)
  events : event Queue.t;  (** the events, that the observers see *)
  mutable sliced_at : float;
      (** the time of [clock], at which the thread, that runs, started its time
          slice, see [Make.Threads], which the pauses of the script shift, as
          the thread doesn't run, while it is paused *)
  mutable resumed : bool;
      (** the thread, that paused, runs, before it is preempted *)
  mutable hooked_at : int64 option;
      (** the address, at which a hook of the code paused the program, before
          its instruction ran, which runs, before the thread is preempted *)
}

(* the folder, and its parents, which are made, if they aren't there *)
let rec mkdirs dir =
  if not (Stdlib.Sys.file_exists dir) then begin
    ignore (mkdirs (Stdlib.Filename.dirname dir) : string);
    try Stdlib.Sys.mkdir dir 0o755 with Sys_error _ -> ()
  end;
  dir

let default_options () =
  {
    timeout = None;
    checkpoint = None;
    restore = None;
    native_stubs = String.Set.of_list Native.names;
    jit = true;
    cache = None;
    digest = "";
  }

let unicorn_options = default_options ()
let lifted_options = default_options ()

let options : kind -> options = function
  | `Unicorn -> unicorn_options
  | `Lifted -> lifted_options

let create_session ?restore ?(engine : kind = `Unicorn) () =
  let o = options engine in
  let restore = Option.value restore ~default:o.restore in
  {
    lifted = Poly.equal engine `Lifted;
    jit = o.jit;
    cache = o.cache;
    digest = o.digest;
    lifter = None;
    active = None;
    recipe = None;
    parked = Id.Table.create ();
    parked_pages = 0;
    dead = Id.Hash_set.create ();
    own_code = Addr.Table.create ();
    stubs = Addr.Table.create ();
    native_stubs = o.native_stubs;
    natives = String.Table.create ();
    signatures = String.Table.create ();
    names = Int64.Table.create ();
    symbols = Int64.Table.create ();
    unstubbed = Int64.Hash_set.create ();
    thumb = Addr.Hash_set.create ();
    thumb_symbols = Int64.Hash_set.create ();
    bare_mode = false;
    timeout = o.timeout;
    accounted = clock ();
    ticks = 0;
    checkpoint = o.checkpoint;
    checkpoint_addr = None;
    checkpointed = false;
    restore;
    restored_from = None;
    resumed_at = None;
    skipped_at = None;
    stops_seen = -1;
    stepping = false;
    stop_addrs = Int64.Hash_set.create ();
    driven = false;
    pause = false;
    saved = Ok ();
    spawned = Error "no thread spawned";
    starts = 0;
    stopped_at = None;
    restarted_at = None;
    call_hooks = String.Table.create ();
    exit_code = None;
    engine_hooks = [];
    events = Queue.create ();
    sliced_at = 0.;
    resumed = false;
    hooked_at = None;
  }

(* the session of the system, which [Loader.init] creates *)
let session_state =
  Primus.Machine.State.declare ~uuid:"6b1e9d42-0f3a-4c87-a5d6-2e8b7f913c50"
    ~name:"unicorn-session" (fun _ -> create_session ())

(* The sessions, which the scripts create for the systems, that they
   run, see [Bap_emu.create], by the numbers, which their projects have,
   see [session_tag], until the systems start, see [Loader.init]. *)
let sessions : session Int.Table.t = Int.Table.create ()

let session_tag =
  Bap.Std.Value.Tag.register
    (module Int)
    ~name:"primus-unicorn-session" ~uuid:"e47c2a91-3d6b-4f08-b5e1-8a9c0d7f6243"

let next_session = ref 0

(* the project, whose system has the session *)
let with_session proj session =
  incr next_session;
  Hashtbl.set sessions ~key:!next_session ~data:session;
  Project.set proj session_tag !next_session

(* the seconds that the machine has run *)
let elapsed =
  Primus.Machine.State.declare ~uuid:"ccde44e4-b82f-4627-80ff-8f5ea918e960"
    ~name:"unicorn-elapsed" (fun _ -> 0.)

(* the pending returns of the runs of a machine, the innermost first,
   which are of the machine, as the machines may switch, while a stub
   runs, and stay when a machine raises an exception, which it doesn't
   survive, as the Primus exceptions are not handled *)
let frames =
  Primus.Machine.State.declare ~uuid:"d47083aa-ead6-439d-8a0c-6bc2bbcc9d6e"
    ~name:"unicorn-frames" (fun _ -> [])

(* if the slots of the external functions refer to their trampolines
   in the memory of the machine, see [Make.link_slots] *)
let slotted =
  Primus.Machine.State.declare ~uuid:"0c7f3d55-2b8e-4f4a-9a5e-62f1d1b0e7a4"
    ~name:"unicorn-slotted" (fun _ -> false)

(* a machine restores the checkpoint once, and its forks don't *)
let restored =
  Primus.Machine.State.declare ~uuid:"8c3f7a52-1d4e-4b9a-9f0e-6a2d5c7b8e41"
    ~name:"unicorn-restored" (fun _ -> false)

(* the functions, that the runs of a machine run, and the stubs, that
   called them, e.g., in Lisp, as its frames, see [frames], which the
   checkpoints keep *)
let calls : (string option * string option) list Primus.Machine.State.t =
  Primus.Machine.State.declare ~uuid:"b5e2d8a4-6c13-4f97-8e0b-3a9d1c7f2e65"
    ~name:"unicorn-calls" (fun _ -> [])

(* the Lisp stubs, that the machine runs, the innermost first *)
let lisp_calls : string list Primus.Machine.State.t =
  Primus.Machine.State.declare ~uuid:"4d7a1e93-b2c8-4f05-9a6e-e1f3b0c82d57"
    ~name:"unicorn-lisp-calls" (fun _ -> [])

(* The threads of the program, that the system calls of Linux create,
   e.g., clone, or the functions of Windows, e.g., CreateThread, which
   run in the same engine, and share its memory, one at a time, see
   [Make.Threads]. A thread, that doesn't run, keeps the values of its
   registers in the variables of Primus, see [thread_var], so that they
   keep their taint and their formulas, and the checkpoints keep them,
   and the address, from which it continues. *)
type wait =
  | Ready
  | Waiting of int64 list
      (** on the addresses, e.g., of the futexes, or of the objects of Windows,
          until one of them is woken *)

type thread = {
  tid : int;
  saved_extra : (int * string) list;
      (** the registers, that Primus doesn't have, e.g., of TLS, see
          [Make.Threads.extra] *)
  next : int64;  (** the address, from which it continues *)
  wait : wait;
  clear : int64 option;
      (** the address of its TID, which is cleared, when it exits, see
          set_tid_address *)
  woken : bool;
      (** if it was woken from its wait, e.g., in the function of Windows, that
          it calls again, see [Make.Threads.Windows] *)
}

type threads = {
  current : int;  (** the TID of the thread, that runs *)
  cleared : int64 option;  (** its [clear] *)
  others : thread list;  (** the threads, that don't run, in their order *)
  last : int;  (** the last TID *)
  depth : int option;
      (** the number of the pending returns, at which the threads switch, which
          is of the run, that created the first thread, see [frames] *)
  woken : bool;  (** the [woken] of the thread, that runs *)
}

(* the threads of a program, that runs at once, at most, as the program,
   which may be hostile, would make the switches of the threads, and the
   memory of their states, unbounded *)
let max_threads = 1024

(* the threads, that a program creates, at most, as the registers of
   each one, that ended, stay in the environment of Primus *)
let max_created = 0x10000

let too_many_threads st =
  List.length st.others >= max_threads || st.last >= max_created

(* the registers of a thread, that Primus doesn't have, e.g., of TLS,
   which the checkpoints keep too *)
let extra_regs (e : engine) =
  (match e.arch with
    | X86 -> [ "FS_BASE"; "GS_BASE"; "MXCSR" ]
    | Arm64 -> [ "TPIDR_EL0"; "FPCR"; "FPSR" ]
    | Arm -> [ "C13_C0_3"; "FPSCR" ]
    | Mips -> [ "CP0_USERLOCAL" ]
    | Ppc -> [ "XER"; "FPSCR" ]
    | _ -> [])
  |> List.filter_map ~f:(Uc.reg e.arch)

(* the bases of the segments of x86 in the protected mode, which Unicorn
   reads, but doesn't write, as they are in the descriptors, see
   [Target.Segments] *)
let segment_base (e : engine) id =
  match e.arch with
  | X86 when e.bytes = 4 ->
      List.find [ "FS_BASE"; "GS_BASE" ] ~f:(fun name ->
          Option.equal Int.equal (Uc.reg X86 name) (Some id))
  | _ -> None

(* the base of the segment is in its descriptor, if the table is mapped,
   as Unicorn reads only FS_BASE in the protected mode *)
let read_extra (e : engine) id =
  match segment_base e id with
  | Some name -> Target.Segments.get e.uc name
  | None -> Uc.reg_read_bytes e.uc id

(* the registers, that aren't the extra ones, e.g., of a checkpoint, that
   is crafted, are not written, as they may be the registers of the
   system, e.g., CR3 of x86 *)
let write_extra (e : engine) id data =
  if not (List.mem (extra_regs e) id ~equal:Int.equal) then ()
  else
    match segment_base e id with
    | Some name ->
        let base =
          String.foldi data ~init:0L ~f:(fun i acc c ->
              Int64.(acc lor (of_int (Char.to_int c) lsl Int.(8 * i))))
        in
        ignore (Target.Segments.set e.uc name base : bool)
    | None -> Uc.reg_write_bytes e.uc id data

(* the variable of the register [v] of the thread, that doesn't run,
   which are made once, as the threads switch often *)
let thread_vars = Hashtbl.Poly.create ()

let thread_var tid v =
  Hashtbl.find_or_add thread_vars
    (tid, Var.name v)
    ~default:(fun () ->
      Var.create (sprintf "thread_%d_%s" tid (Var.name v)) (Var.typ v))

let threads =
  Primus.Machine.State.declare ~uuid:"2f6c8e1a-9b3d-4c7e-a5f0-7d1e4b8c9a36"
    ~name:"unicorn-threads" (fun _ ->
      {
        current = 1;
        cleared = None;
        others = [];
        last = 1;
        depth = None;
        woken = false;
      })

(* What a stub does, after the function, that it called, returns, e.g.,
   __libc_start_main exits with the result of main, as the run of the
   function continues from a checkpoint, without the stub, whose code is
   not data, see [Checkpoint] *)
module type Completion = functor (Machine : Primus.Machine.S) -> sig
  val complete : callee:string option -> unit Machine.t
end

let completions : (module Completion) String.Table.t = String.Table.create ()

let complete name completion =
  Hashtbl.set completions ~key:name ~data:completion

(* the number of the pages, that are parked, after which only the
   pending pages are, as the forks may be many *)
let parked_limit = 16384

let unpark_all s id =
  Option.iter (Hashtbl.find_and_remove s.parked id) ~f:(fun pages ->
      s.parked_pages <- s.parked_pages - Hashtbl.length pages)

(* The script, that drives the machines, see [Bap_emu]. A machine
   pauses before Unicorn runs, when the script asks, and serves the
   requests of the script, e.g., to copy a page to Unicorn, until the
   script continues it, from an address. The machines run in the fiber
   of the script, which they pause with the [Paused] effect. *)
type request =
  | Continue of int64
  | Map of int64
  | Snapshot  (** the machine forks, and its parent stays, see [Make.serve] *)
  | Restore of Primus.Machine.id
      (** the machine is killed, and a fork of the snapshot continues *)
  | Store of int64 * string
      (** the bytes are stored to the memory of Primus, see [Bap_emu.write] *)
  | Run of Primus.Machine.component
      (** the component runs in the machine, see [Bap_emu.primus] *)
  | Set_pc of int64
      (** the machine continues from the address, when it continues, see
          [Bap_emu.set_pc] *)
  | Interpret
      (** the instruction, at which the machine paused, runs in Primus, as its
          lifted semantics, see [Bap_emu.interpret] *)
  | Save of string * int64
      (** the checkpoint of the machine, which continues from the address, is
          saved to the file, see [Bap_emu.save] *)
  | Spawn of int64 * int64 * int64 option
      (** the thread, that calls the function at the address with the argument,
          on the stack, is created, see [Bap_emu.spawn_thread] *)

type _ Effect.t +=
  | Paused : int64 * Primus.Machine.id -> request Effect.t
  | Ended : Primus.exit_status -> request Effect.t
        (** the program ended, and the script may restore a snapshot *)

(* The instructions, e.g., the system calls, which the lifters represent
   as the calls to the intrinsic functions, e.g., intrinsic:syscall, with
   the inputs in the variables intrinsic:x0, intrinsic:x1, etc., are run
   by the Primus linker, as the interpreter does, when they stop Unicorn
   with an interrupt, after which Unicorn continues from the next
   instruction. *)
type intrinsic = {
  name : string;
  inputs : (var * exp) list;
  outputs : (var * exp) list;
      (** the defs after the call, e.g., of the registers, that the results of
          the intrinsic, intrinsic:y0, ..., go to *)
}

(* the intrinsic of the instruction, which the blocks of its IR call *)
let site_of_blocks blks =
  let defs =
    List.concat_map blks ~f:(fun blk -> Term.enum def_t blk |> Seq.to_list)
  in
  (* the defs of the blocks after the one, that calls *)
  let after blk =
    match List.drop_while blks ~f:(fun b -> not (phys_equal b blk)) with
    | _ :: rest ->
        List.concat_map rest ~f:(fun blk ->
            Term.enum def_t blk |> Seq.to_list
            |> List.map ~f:(fun def -> (Def.lhs def, Def.rhs def)))
    | [] -> []
  in
  List.find_map blks ~f:(fun blk ->
      Term.enum jmp_t blk
      |> Seq.find_map ~f:(fun jmp ->
          match Jmp.kind jmp with
          | Call call -> (
              match Call.target call with
              | Direct tid ->
                  let name =
                    String.chop_prefix_if_exists (Tid.name tid) ~prefix:"@"
                  in
                  Option.some_if
                    (String.is_prefix name ~prefix:"intrinsic:")
                    {
                      name;
                      inputs =
                        List.filter_map defs ~f:(fun def ->
                            Option.some_if
                              (String.is_prefix
                                 (Var.name (Def.lhs def))
                                 ~prefix:"intrinsic:")
                              (Def.lhs def, Def.rhs def));
                      outputs = after blk;
                    }
              | Indirect _ -> None)
          | Goto _ | Ret _ | Int _ -> None))

(* the exceptions of Unicorn, that it raises at the instruction, which
   doesn't run, e.g., the breakpoints of ARM, and the faults of x86, the
   others, e.g., the system calls, are raised after the instruction *)
let raised_at (arch : Uc.arch) n =
  match arch with
  | Arm | Arm64 -> n = 1 || n = 7
  | X86 -> n >= 0 && n < 32 && n <> 3 && n <> 4
  | _ -> false

let index_thumb_symbols { thumb_symbols; _ } spec =
  Hash_set.clear thumb_symbols;
  (* the entry point, which the stripped program has no symbol for *)
  (match Ogre.eval (Ogre.request Image.Scheme.entry_point) spec with
  | Ok (Some entry) when Int64.(entry land 1L = 1L) ->
      Hash_set.add thumb_symbols Int64.(entry land lnot 1L)
  | _ -> ());
  match
    Ogre.eval
      (Ogre.collect Ogre.Query.(select (from Image.Scheme.symbol_value)))
      spec
  with
  | Error _ -> ()
  | Ok values ->
      Seq.iter values ~f:(fun (addr, value) ->
          if Int64.(value land 1L = 1L) then
            Hash_set.add thumb_symbols Int64.(addr land lnot 1L))

let is_thumb { thumb_symbols; _ } sub =
  match Term.first blk_t sub with
  | None -> (
      match Term.get_attr sub address with
      | Some addr ->
          Hash_set.mem thumb_symbols
            Int64.(Bitvec.to_int64 (Word.to_bitvec addr) land lnot 1L)
      | None -> false)
  | Some blk -> (
      let insn =
        match Term.first def_t blk with
        | Some def -> Term.get_attr def Disasm.insn
        | None ->
            Option.bind (Term.first jmp_t blk) ~f:(fun jmp ->
                Term.get_attr jmp Disasm.insn)
      in
      match insn with
      | Some insn -> String.is_prefix (Insn.name insn) ~prefix:"t"
      | None -> false)

let int64_of_word w = Bitvec.to_int64 (Word.to_bitvec w)

let var_of_reg v =
  Var.create (Theory.Var.name v)
    (Type.imm (Theory.Bitv.size (Theory.Var.sort v)))

let is_alias target v =
  Theory.Target.has_roles target [ Theory.Role.Register.alias ] v

let reg_of_role target role =
  Option.bind (Theory.Target.reg target role) ~f:(fun v ->
      Option.map
        (Theory.Bitv.refine (Theory.Var.sort v))
        ~f:(fun s ->
          Var.create (Theory.Var.name v) (Type.imm (Theory.Bitv.size s))))

(* the register that holds the return address *)
let link_register target (arch : Uc.arch) =
  let bits = Theory.Target.bits target in
  let reg name = Some (Var.create name (Type.imm bits)) in
  match arch with
  | X86 -> None
  | Arm | Ppc -> reg "LR"
  | Arm64 -> reg "R30"
  | Mips -> reg "R31"
  | Riscv -> reg "X1"

let failf fmt = ksprintf (fun msg -> raise (Unsupported msg)) fmt

(* The external functions, which the code calls through the slots that
   the dynamic linker fills, get the addresses in a reserved region,
   which is never mapped in Primus, and the slots of the pages copied
   to Unicorn refer to them. *)
let trampolines_base target =
  if Theory.Target.bits target = 64 then 0x7FFF_FFF0_0000L else 0xFFFF_0000L

let trampoline_size = 16L

(* the instruction that does nothing, which fills the trampolines, since
   Unicorn raises an interrupt, before it calls the hooks of the address,
   if the instruction is invalid, as the zeros are on RISC-V *)
let nop (arch : Uc.arch) ~big_endian =
  let word ~big x =
    String.init 4 ~f:(fun i ->
        let i = if big then 3 - i else i in
        Char.of_int_exn ((x lsr (8 * i)) land 0xFF))
  in
  match arch with
  | X86 -> "\x90"
  (* andeq r0, r0, r0 and sll $0, $0, 0 *)
  | Arm | Mips -> "\000\000\000\000"
  | Arm64 -> word ~big:false 0xD503201F
  | Ppc -> word ~big:big_endian 0x60000000
  | Riscv -> word ~big:false 0x13

let halt_at e reason =
  e.reason <- Some reason;
  Uc.stop e.uc

(* the stops of the system, as they were, when Unicorn started, see
   [Make.sync_stops] *)
let is_stop e addr =
  e.session.stepping || Hash_set.mem e.session.stop_addrs addr

(* the hook of the address of the checkpoint or of a stop, which skips
   the address, from which the machine continues, see [resumed_at], and,
   while stepping, the next hook of the same instruction, which is the
   hook of every address *)
let dispatch e addr =
  let s = e.session in
  let stepping = s.stepping in
  (match s.skipped_at with
  | Some at when stepping && Int64.(at <> addr) -> s.skipped_at <- None
  | _ -> ());
  match s.resumed_at with
  | Some at when Int64.(at = addr) ->
      s.resumed_at <- None;
      s.skipped_at <- Some addr
  | _ when stepping && Option.equal Int64.equal s.skipped_at (Some addr) -> ()
  | _ ->
      if
        Option.equal Int64.equal s.checkpoint_addr (Some addr)
        && not s.checkpointed
      then halt_at e Checkpoint
        (* the observers of every address see the stops too, see [watch] *)
      else if is_stop e addr && not e.watching.pcs then halt_at e (Stop addr)

(* The instructions, which read the tracked registers, are interpreted
   by Primus, as the analyses, that track them, e.g., taint, see their
   computations, so Unicorn stops before them, and before the ones, which
   it didn't see yet, or whose bytes changed, e.g., which the program
   wrote, after which they are analyzed, see [Make.analyze].
   The tracked registers, that the code writes, are not tracked anymore,
   and Primus gets their values, see [Make.pull_regs] *)
let trace e addr =
  let unchanged { code; _ } =
    String.is_empty code
    ||
    match Uc.mem_read e.uc addr (String.length code) with
    | bytes -> String.equal bytes code
    | exception Uc.Error _ -> false
  in
  match Hashtbl.find e.accesses addr with
  | Some ({ uses; defs; _ } as access) when unchanged access ->
      if List.exists uses ~f:(Hash_set.mem e.tracked) then
        halt_at e (Interpret addr)
      else
        List.iter defs ~f:(fun r ->
            if Hash_set.mem e.tracked r then begin
              Hash_set.remove e.tracked r;
              e.clobbered <- r :: e.clobbered
            end)
  | _ -> halt_at e (Unknown addr)

(* the hook of every address is installed, while a register is tracked,
   and the translated code is dropped, see [sync_stops] *)
let sync_tracer e =
  match (Hash_set.is_empty e.tracked, e.tracer) with
  | false, None ->
      e.tracer <- Some (Uc.on_code e.uc (fun addr _ -> trace e addr));
      Uc.flush_tb e.uc
  | true, Some hook ->
      Uc.delete e.uc hook;
      e.tracer <- None;
      Uc.flush_tb e.uc
  | _ -> ()

(* the registers of the basis, that the instruction reads and writes *)
let access_of_blocks regs ~code blks =
  let owner v =
    if Var.is_physical v then Target.Regs.owner regs (Var.name v) else None
  in
  let exps =
    List.concat_map blks ~f:(fun blk ->
        (Term.enum def_t blk |> Seq.map ~f:Def.rhs |> Seq.to_list)
        @ (Term.enum jmp_t blk |> Seq.to_list
          |> List.concat_map ~f:(fun jmp ->
              let labels =
                match Jmp.kind jmp with
                | Goto l | Ret l -> [ l ]
                | Call c -> Call.target c :: Option.to_list (Call.return c)
                | Int _ -> []
              in
              Jmp.cond jmp
              :: List.filter_map labels ~f:(function
                | Indirect x -> Some x
                | Direct _ -> None))))
  in
  let memory =
    List.exists exps ~f:(fun x ->
        object
          inherit [bool] Exp.visitor
          method! enter_load ~mem:_ ~addr:_ _ _ _ = true
          method! enter_store ~mem:_ ~addr:_ ~exp:_ _ _ _ = true
        end
          #visit_exp x false)
  in
  let uses =
    List.concat_map exps ~f:(fun x -> Set.to_list (Exp.free_vars x))
    |> List.filter_map ~f:owner
    |> List.dedup_and_sort ~compare:String.compare
  in
  let defs =
    match blks with
    | [ blk ] ->
        Term.enum def_t blk |> Seq.to_list
        |> List.filter_map ~f:(fun def ->
            let v = Def.lhs def in
            match owner v with
            | Some r when String.equal r (Var.name v) -> Some r
            | _ -> None)
    | _ -> []
  in
  { uses; defs; memory; code }

let hook_stop e addr =
  if not (Hash_set.mem e.hooked addr) then begin
    Hash_set.add e.hooked addr;
    ignore
    @@ Uc.on_code e.uc ~first:addr ~last:addr (fun _ _ -> dispatch e addr)
  end

(* the stops, which changed, are hooked, and the hook of every address
   is added or deleted, as the stepping is on or off, after which the
   translated code is dropped, as the hooks apply only to the code that
   Unicorn translates after them *)
let sync_stops e =
  let version = e.session.stops_seen in
  if e.stops <> version then begin
    e.stops <- version;
    Hash_set.iter e.session.stop_addrs ~f:(hook_stop e);
    (match (e.session.stepping, e.stepper) with
    | true, None ->
        e.stepper <- Some (Uc.on_code e.uc (fun addr _ -> dispatch e addr))
    | false, Some hook ->
        Uc.delete e.uc hook;
        e.stepper <- None
    | _ -> ());
    Uc.flush_tb e.uc
  end

(* if the instruction of MIPS is a branch or a jump, which has a delay
   slot, by its encoding: J, JAL, BEQ, BNE, BLEZ, BGTZ, and their likely
   forms, the branches of REGIMM, e.g., BLTZ and BGEZAL, JR and JALR of
   SPECIAL, and BC1 of COP1. The release 6 has no likely forms, its
   compact branches, e.g., BEQC of the former opcodes of BLEZL, or of
   BLEZ, whose rt isn't 0, have no delay slots, and its BC1EQZ and
   BC1NEZ have *)
let mips_delayed ~r6 word =
  let op = Int64.(to_int_exn ((word lsr 26) land 0x3FL)) in
  let rs = Int64.(to_int_exn ((word lsr 21) land 0x1FL)) in
  let rt = Int64.(to_int_exn ((word lsr 16) land 0x1FL)) in
  let funct = Int64.(to_int_exn (word land 0x3FL)) in
  match op with
  | 0x02 | 0x03 | 0x04 | 0x05 -> true
  | 0x06 | 0x07 -> (not r6) || rt = 0
  | 0x14 | 0x15 | 0x16 | 0x17 -> not r6
  | 0x01 ->
      List.mem
        (if r6 then [ 0x00; 0x01; 0x10; 0x11 ]
         else [ 0x00; 0x01; 0x02; 0x03; 0x10; 0x11; 0x12; 0x13 ])
        rt ~equal:Int.equal
  | 0x00 -> funct = 0x08 || funct = 0x09
  | 0x11 -> if r6 then rs = 0x09 || rs = 0x0D else rs = 0x08
  | _ -> false

(* if the branch of MIPS, which has a delay slot, is likely, whose delay
   slot runs only if it is taken: BEQL, BNEL, BLEZL, BGTZL, the likely
   branches of REGIMM, and BC1FL and BC1TL, the release 6 has none *)
let mips_likely ~r6 word =
  let op = Int64.(to_int_exn ((word lsr 26) land 0x3FL)) in
  let rs = Int64.(to_int_exn ((word lsr 21) land 0x1FL)) in
  let rt = Int64.(to_int_exn ((word lsr 16) land 0x1FL)) in
  (not r6)
  &&
  match op with
  | 0x14 | 0x15 | 0x16 | 0x17 -> true
  | 0x01 -> List.mem [ 0x02; 0x03; 0x12; 0x13 ] rt ~equal:Int.equal
  | 0x11 -> rs = 0x08 && rt land 2 <> 0
  | _ -> false

(* if the instruction of the release 6 of MIPS is a conditional compact
   branch, whose forbidden slot, the next instruction, runs only if it
   isn't taken: of POP06, POP07, POP26, and POP27, whose rt isn't 0, or
   of POP10 and POP30, or BEQZC and BNEZC, whose rs isn't 0 *)
let mips_compact word =
  let op = Int64.(to_int_exn ((word lsr 26) land 0x3FL)) in
  let rs = Int64.(to_int_exn ((word lsr 21) land 0x1FL)) in
  let rt = Int64.(to_int_exn ((word lsr 16) land 0x1FL)) in
  match op with
  | 0x06 | 0x07 | 0x16 | 0x17 -> rt <> 0
  | 0x08 | 0x18 -> true
  | 0x36 | 0x3E -> rs <> 0
  | _ -> false

(* the targets of the release 6 of MIPS, by their nicknames, see
   Bap_mips_target *)
let mips_r6 target =
  List.exists
    [ "mipsisa32r6"; "mipsisa32r6el"; "mipsisa64r6"; "mipsisa64r6el" ]
    ~f:(Theory.Target.matches target)

(* lifts the instruction for the lifted engine, outside of the machine,
   in the knowledge, that starts from the toplevel one, and keeps the
   semantics, e.g., the Primus Lisp program of x86, as Bap_emu lifts the
   instructions in the hooks *)
(* The instructions, that the lifter lifted, in the other runs of the
   program, which the lifted engine runs, rather than it lifts them again,
   whose file is in the cache, by the digest of the version of BAP, the
   configuration of its plugins, the file of the program, and its target,
   see [lifter]. The labels of the calls, e.g., of the intrinsics, are
   the objects of the knowledge of the run, that lifted them, which are
   made anew, when they are read, with their names. *)
module Lifts = struct
  type entry = {
    addr : int64;
    thumb : bool;
    code : string;
    size : int;
    name : string;
    blks : blk term list;
    calls : (tid * string) list;
  }
  [@@deriving bin_io]

  type t = entry list [@@deriving bin_io]

  let magic = "bap-lifted-lifts 1\n"

  let load file =
    try
      let data = In_channel.read_all file in
      if String.is_prefix data ~prefix:magic then
        Binable.of_string
          (module struct
            type nonrec t = t [@@deriving bin_io]
          end)
          (String.drop_prefix data (String.length magic))
      else []
    with _ -> []

  let save file entries =
    try
      let tmp =
        Stdlib.Filename.temp_file
          ~temp_dir:(Stdlib.Filename.dirname file)
          (Stdlib.Filename.basename file)
          ".tmp"
      in
      Out_channel.with_file ~binary:true tmp ~f:(fun out ->
          Out_channel.output_string out magic;
          Out_channel.output_string out
            (Binable.to_string
               (module struct
                 type nonrec t = t [@@deriving bin_io]
               end)
               entries));
      Stdlib.Sys.rename tmp file
    with _ -> ()
end

(* The intrinsics of x86, that Unicorn runs natively, and that Primus
   and the lifted engine call, see CPUID of x86-control.lisp: CPUID and
   XGETBV run in a Unicorn of their own, of the mode of the target, so
   that they report the processor of Unicorn, and their results are
   cached, and the time stamp counter is the monotonic clock, in ns. *)
module X86_intrinsics = struct
  let scratch = Hashtbl.Poly.create ()
  let results = Hashtbl.Poly.create ()
  let code_addr = 0x1000L

  let uc mode =
    Hashtbl.find_or_add scratch mode ~default:(fun () ->
        let uc = Uc.create X86 mode in
        Uc.mem_map uc code_addr 0x1000L Uc.Perm.(read + exec);
        uc)

  let reg name = Option.value_exn (Uc.reg X86 name)

  (* the registers RAX, RBX, RCX, RDX after the instruction [code], that
     runs from RAX = [a] and RCX = [c], or [None], if it faults *)
  let run mode code a c =
    Hashtbl.find_or_add results (mode, code, a, c) ~default:(fun () ->
        let uc = uc mode in
        Uc.mem_write uc code_addr code;
        (* Unicorn runs the code, that it translated, unless it flushes it *)
        Uc.flush_tb uc;
        List.iter [ "RAX"; "RBX"; "RCX"; "RDX" ] ~f:(fun r ->
            Uc.reg_write uc (reg r) 0L);
        Uc.reg_write uc (reg "RAX") a;
        Uc.reg_write uc (reg "RCX") c;
        match Uc.start ~count:1 uc code_addr with
        | () ->
            Some
              (List.map [ "RAX"; "RBX"; "RCX"; "RDX" ] ~f:(fun r ->
                   Int64.(Uc.reg_read uc (reg r) land 0xFFFF_FFFFL)))
        | exception Uc.Error _ -> None)

  let tsc () = Int64.of_float (clock () *. 1e9)
end

let lifter ?cache ~arm project =
  let state = ref None in
  let names = Tid.Table.create () in
  let entries = Hashtbl.Poly.create () in
  let dirty = ref false in
  let save () =
    Option.iter cache ~f:(fun file ->
        if !dirty then begin
          dirty := false;
          Lifts.save file (Hashtbl.data entries |> List.map ~f:fst)
        end)
  in
  Option.iter cache ~f:(fun file ->
      List.iter (Lifts.load file) ~f:(fun (e : Lifts.entry) ->
          Hashtbl.set entries ~key:(e.addr, e.thumb) ~data:(e, ref false));
      at_exit save;
      (* the run, that a signal terminates, e.g., the timeout of a
         script, exits, so that the instructions are saved, and the next
         run starts with them, unless the signal is handled already *)
      List.iter
        [ (Stdlib.Sys.sigterm, 143); (Stdlib.Sys.sigint, 130) ]
        ~f:(fun (signal, code) ->
          match Stdlib.Sys.signal signal Stdlib.Sys.Signal_default with
          | Stdlib.Sys.Signal_default ->
              Stdlib.Sys.set_signal signal
                (Stdlib.Sys.Signal_handle (fun _ -> Stdlib.exit code))
          | handler -> Stdlib.Sys.set_signal signal handler));
  (* the names of the labels, that the instruction calls, e.g., of the
     intrinsics, @intrinsic:fadd_rne_ieee754_binary_64, in the knowledge
     of the lifter *)
  let called blks =
    List.iter blks ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.iter ~f:(fun jmp ->
            match Jmp.kind jmp with
            | Call call -> (
                match Call.target call with
                | Direct tid -> (
                    match String.chop_prefix (Tid.name tid) ~prefix:"@" with
                    | Some name -> Hashtbl.set names ~key:tid ~data:name
                    | None -> ())
                | Indirect _ -> ())
            | _ -> ()))
  in
  (* the labels of the calls of the instruction, that are made anew, in
     the toplevel knowledge, once, with their names, as the labels of the
     knowledge of the lifter are dropped with it, see [in_state], or are
     of the cache *)
  let fresh (e : Lifts.entry) =
    let renamed =
      List.map e.calls ~f:(fun (tid, name) ->
          let tid' = Tid.create () in
          Hashtbl.set names ~key:tid' ~data:name;
          (tid, tid'))
    in
    let rename tid =
      List.Assoc.find renamed tid ~equal:Tid.equal |> Option.value ~default:tid
    in
    let blks =
      List.map e.blks ~f:(fun blk ->
          Term.map jmp_t blk ~f:(fun jmp ->
              match Jmp.kind jmp with
              | Call call -> (
                  match Call.target call with
                  | Direct tid ->
                      Jmp.with_kind jmp
                        (Call (Call.with_target call (Direct (rename tid))))
                  | Indirect _ -> jmp)
              | _ -> jmp))
    in
    {
      e with
      blks;
      calls = List.map e.calls ~f:(fun (tid, name) -> (rename tid, name));
    }
  in
  (* the knowledge of the lifter, in which [f] runs: the knowledge after
     the lifts, that take long, e.g., the first one, which loads the
     semantics, e.g., the Lisp program of x86, is kept, and the
     knowledge after the other lifts is dropped, so that it doesn't grow
     with the instructions, that are lifted, whose labels, code and
     semantics it would keep, see Primus.Lift; the labels, that the
     dropped knowledge made, e.g., of the calls, are made anew, see
     [fresh] *)
  let in_state f =
    let toplevel = Toplevel.current () in
    Toplevel.set (Option.value !state ~default:toplevel);
    let started = clock () in
    Exn.protect
      ~finally:(fun () ->
        if Option.is_none !state || Float.(clock () -. started > 0.1) then
          state := Some (Toplevel.current ());
        Toplevel.set toplevel)
      ~f
  in
  let lift ~thumb addr code =
    match Hashtbl.find entries (addr, thumb) with
    | Some (e, renamed) when String.is_prefix code ~prefix:e.code ->
        let e =
          if !renamed then e
          else begin
            let e = fresh e in
            Hashtbl.set entries ~key:(addr, thumb) ~data:(e, ref true);
            e
          end
        in
        Some (e.size, e.name, e.blks)
    | _ ->
        let result = ref None in
        in_state (fun () ->
            try
              Toplevel.exec
                KB.Syntax.(
                  Primus.Lift.named
                    ?encoding:
                      (if arm then Primus.Interworking.encoding ~thumb else None)
                    project addr code
                  >>| fun insn ->
                  result := insn;
                  Option.iter insn ~f:(fun (_, _, blks) -> called blks))
            with _ -> ());
        (* the instruction is kept for the engines of the session, e.g., of
           the forks, and for the cache, if there is one, with the labels
           of its calls made anew, see [fresh] *)
        Option.map !result ~f:(fun (size, name, blks) ->
            if size <= String.length code then begin
              let calls =
                List.concat_map blks ~f:(fun blk ->
                    Term.enum jmp_t blk |> Seq.to_list
                    |> List.filter_map ~f:(fun jmp ->
                        match Jmp.kind jmp with
                        | Call call -> (
                            match Call.target call with
                            | Direct tid ->
                                Option.map (Hashtbl.find names tid)
                                  ~f:(fun name -> (tid, name))
                            | Indirect _ -> None)
                        | _ -> None))
              in
              let e =
                fresh
                  {
                    Lifts.addr;
                    thumb;
                    code = String.prefix code size;
                    size;
                    name;
                    (* the engine doesn't read the attributes, e.g., the
                       instructions, which are most of the file *)
                    blks =
                      List.map blks ~f:(fun blk ->
                          let blk =
                            Term.map def_t blk ~f:(fun t ->
                                Term.with_attrs t Dict.empty)
                            |> Term.map jmp_t ~f:(fun t ->
                                Term.with_attrs t Dict.empty)
                          in
                          Term.with_attrs blk Dict.empty);
                    calls;
                  }
              in
              Hashtbl.set entries ~key:(addr, thumb) ~data:(e, ref true);
              dirty := true;
              (size, name, e.blks)
            end
            else (size, name, blks))
  in
  {
    lift;
    name = Hashtbl.find names;
    cached = not (Hashtbl.is_empty entries);
    save;
  }

(* the NaNs and the invalid integers of the target, as ieee754-policy of
   ieee754-intrinsics.lisp *)
let ieee754_policy target =
  if Theory.Target.matches target "x86" then 0x15
  else if Theory.Target.matches target "riscv" then 0x22
  else if Theory.Target.matches target "powerpc-family" then 0x34
  else if Theory.Target.matches target "mips-family" then 0x20
  else 0

(* the delay slots of the branches, of MIPS, by their encodings *)
let delay_of target (arch : Uc.arch) =
  let r6 = mips_r6 target in
  let big = Theory.Endianness.(equal eb) (Theory.Target.endianness target) in
  fun code ->
    match arch with
    | Mips when String.length code >= 4 ->
        let word =
          List.init 4 ~f:(fun i -> Char.to_int code.[if big then i else 3 - i])
          |> List.fold ~init:0L ~f:(fun acc b ->
              Int64.((acc lsl 8) lor of_int b))
        in
        if mips_likely ~r6 word then `Likely
        else if mips_delayed ~r6 word then `Delayed
        else if r6 && mips_compact word then `Forbidden
        else `None
    | _ -> `None

let create session target ~foreign ~externals =
  let arch, mode =
    match Target.engine target with
    | Some e -> e
    | None ->
        failf "the target %s is not supported" (Theory.Target.to_string target)
  in
  (* the registers of BAP, that the lifted engine runs, are located, when
     the engine is created, see [regs] *)
  let locate = ref (fun _ -> None) and owner = ref (fun _ -> None) in
  let uc =
    match session.lifter with
    | Some { lift; name; _ } when session.lifted ->
        Uc.create_lifted
          {
            lift;
            name;
            policy = ieee754_policy target;
            delay = delay_of target arch;
            locate = (fun name -> !locate name);
            owner = (fun name -> !owner name);
            pc = Target.pc arch mode;
            big_endian =
              Theory.Endianness.(equal eb) (Theory.Target.endianness target);
            bits = Theory.Target.bits target;
            jit = session.jit;
            cache =
              Option.map session.cache ~f:(fun dir -> mkdirs (dir ^/ "objects"));
          }
          arch mode
    | _ -> Uc.create arch mode
  in
  (* the default CPU of AArch64, Cortex-A72, is ARMv8.0, which has no LSE
     atomics of ARMv8.1, e.g., ldadd and cas, that the programs compiled
     for the later ones, or with outline atomics, run; the maximum one has
     all of them, and must be selected before anything else *)
  (match arch with Arm64 -> Uc.set_cpu_model uc Uc.Cpu.arm64_max | _ -> ());
  (* the default CPU of MIPS64, R4000, is MIPS III, which has no
     instructions of the release 2, e.g., seb, and rdhwr, which reads the
     pointer of TLS, that the programs of Linux use *)
  (match arch with
  | Mips when mips_r6 target ->
      Uc.set_cpu_model uc
        (if Theory.Target.bits target = 64 then Uc.Cpu.mips64_i6400
         else Uc.Cpu.mips32r6_generic)
  | Mips when Theory.Target.bits target = 64 ->
      Uc.set_cpu_model uc Uc.Cpu.mips64r2_generic
  | _ -> ());
  (* the addresses of the program are the addresses of Unicorn *)
  Uc.set_tlb_virtual uc;
  (* the 64-bit addresses of MIPS are enabled by the KX, SX, and UX bits *)
  (match arch with
  | Mips when Theory.Target.bits target = 64 ->
      let status = Option.value_exn (Uc.reg Mips "CP0_STATUS") in
      (* and the 64-bit FPU registers, FR, of the n64 ABI *)
      Uc.reg_write uc status Int64.(Uc.reg_read uc status lor 0x040000E0L)
  (* the FPU and AltiVec of PowerPC, which Linux enables, are off at the
     reset, as MSR.FP and MSR.VEC are 0 *)
  | Ppc ->
      Option.iter (Uc.reg Ppc "MSR") ~f:(fun msr ->
          Uc.reg_write uc msr Int64.(Uc.reg_read uc msr lor 0x02002000L))
  (* the FPU of RISC-V, which Linux enables, is off at the reset, as
     mstatus.FS is 0 *)
  | Riscv ->
      Option.iter (Uc.reg Riscv "MSTATUS") ~f:(fun mstatus ->
          Uc.reg_write uc mstatus Int64.(Uc.reg_read uc mstatus lor 0x6000L))
  (* the VFP and NEON of ARM, which Linux enables, are disabled at the
     reset: the coprocessors 10 and 11 are accessible in CPACR, and
     FPEXC enables them *)
  | Arm ->
      Option.iter (Uc.reg Arm "C1_C0_2") ~f:(fun cpacr ->
          Uc.reg_write uc cpacr Int64.(Uc.reg_read uc cpacr lor 0xF00000L));
      Option.iter (Uc.reg Arm "FPEXC") ~f:(fun fpexc ->
          Uc.reg_write uc fpexc 0x40000000L)
  | _ -> ());
  let regs = Target.Regs.create target arch uc in
  (locate := fun name -> Target.Regs.locate regs name);
  (owner := fun name -> Target.Regs.owner regs name);
  let sp =
    match reg_of_role target Theory.Role.Register.stack_pointer with
    | Some sp -> sp
    | None -> failf "the target has no stack pointer"
  in
  let basis = Target.Regs.basis regs in
  let e =
    {
      session;
      uc;
      arch;
      regs;
      pc = Target.pc arch mode;
      sp;
      link = link_register target arch;
      bytes = Theory.Target.bits target / 8;
      basis;
      pages = Int64.Table.create ();
      owner = None;
      reason = None;
      frames = [];
      returns = Int64.Table.create ();
      synced = String.Table.create ();
      written = [];
      unchecked = [];
      dirty = [];
      runs = 0;
      broken = false;
      trampolines = Int64.Table.create ();
      slots = Int64.Table.create ();
      big_endian =
        Theory.Endianness.(equal eb) (Theory.Target.endianness target);
      r6 = mips_r6 target;
      hooked = Int64.Hash_set.create ();
      stops = -1;
      stepper = None;
      watching =
        { pcs = false; reads = false; writes = false; code_writes = false };
      code_segments = [];
      code_written = Int64.Table.create ();
      watchers = [];
      observed = None;
      accesses = Int64.Table.create ();
      foreign = Int64.Hash_set.of_list foreign;
      tracked = String.Hash_set.create ();
      clobbered = [];
      tracer = None;
      seen = -1;
      shadowing = false;
      shadowed = false;
      known = Int.Table.create ();
    }
  in
  let base = trampolines_base target in
  let addrs = String.Table.create () in
  List.iter externals ~f:(fun (slot, name) ->
      let addr =
        Hashtbl.find_or_add addrs name ~default:(fun () ->
            let addr =
              Int64.(base + (of_int (Hashtbl.length addrs) * trampoline_size))
            in
            Hashtbl.set e.trampolines ~key:addr ~data:name;
            addr)
      in
      Hashtbl.add_multi e.slots ~key:(page_of slot)
        ~data:(Int64.(to_int_exn (slot - page_of slot)), addr));
  if not (Hashtbl.is_empty addrs) then begin
    let size =
      Int64.(
        page_of
          ((of_int (Hashtbl.length addrs) * trampoline_size) + page_size - 1L))
    in
    Uc.mem_map uc base size Uc.Perm.(read + exec);
    let nop = nop arch ~big_endian:e.big_endian in
    Uc.mem_write uc base
      (String.concat
         (List.init
            (Int64.to_int_exn size / String.length nop)
            ~f:(fun _ -> nop)));
    ignore
    @@ Uc.on_code uc ~first:base
         ~last:Int64.(base + size - 1L)
         (fun addr _ ->
           e.reason <- Some (Foreign addr);
           Uc.stop uc)
  end;
  let stop reason =
    e.reason <- Some reason;
    Uc.stop uc
  in
  (* the first hook of an address that stops Unicorn is the last one
     called, so the checkpoint goes before the foreign code, which runs
     after it is saved *)
  Option.iter session.checkpoint_addr ~f:(hook_stop e);
  (* the function may run in Unicorn again, see [Make.unstub] *)
  List.iter foreign ~f:(fun addr ->
      ignore
      @@ Uc.on_code uc ~first:addr ~last:addr (fun _ _ ->
          if Hash_set.mem e.foreign addr then stop (Foreign addr)));
  let returns addr =
    match e.frames with
    | { ret; sp } :: _ ->
        Int64.(ret = addr)
        && Int64.(
             int64_of_word (Option.value_exn (Target.Regs.read regs e.sp)) = sp)
    | [] -> false
  in
  ignore
  @@ Uc.on_mem_invalid uc [ `read; `write; `fetch ] [ `unmapped; `prot ]
       (fun access addr _ _ ->
         (match access with
         | Fetch_unmapped when returns addr -> e.reason <- Some Returned
         | _ -> e.reason <- Some (Fault (access, addr)));
         (match (access, arch) with
         | Fetch_unmapped, Mips -> e.broken <- true
         | _ -> ());
         false);
  ignore @@ Uc.on_interrupt uc (fun n -> stop (Interrupt n));
  (match arch with
  | X86 -> ignore @@ Uc.on_x86_syscall uc (fun () -> stop (Interrupt (-1)))
  | _ -> ());
  ignore
  @@ Uc.on_invalid_insn uc (fun () ->
      e.reason <- Some Invalid;
      false);
  (* the instruction, that the lifted engine can't run, is interpreted *)
  ignore @@ Uc.on_unsupported uc (fun addr -> e.reason <- Some (Interpret addr));
  List.iter (List.rev session.engine_hooks) ~f:(fun install -> install e);
  e

let is_owner e id =
  match e.owner with
  | Some owner -> Monads.Std.Monad.State.Multi.Id.equal owner id
  | None -> false

(* the runs of the bytes of [data], that differ from [known], with their
   addresses from [base] *)
let changes base data known =
  let n = Bytes.length data in
  let differs i = not (Char.equal (Bytes.get data i) (Bytes.get known i)) in
  let rec runs i acc =
    if i = n then List.rev acc
    else if not (differs i) then runs (i + 1) acc
    else
      let rec last j =
        if j + 1 < n && differs (j + 1) then last (j + 1) else j
      in
      let j = last i in
      runs (j + 1)
        (( Int64.(base + of_int i),
           Bytes.To_string.sub data ~pos:i ~len:(j - i + 1) )
        :: acc)
  in
  runs 0 []

let read_page e page =
  Bytes.of_string (Uc.mem_read e.uc page (Int64.to_int_exn page_size))

(* the dirty page, which Unicorn may have changed since it was fetched *)
let pending e (p : page) = p.dirty && p.fetched <> e.runs

(* the changed bytes of the dirty pages, that Unicorn may have changed *)
let pending_changes e =
  List.concat_map e.dirty ~f:(fun page ->
      match Hashtbl.find e.pages page with
      | Some ({ snapshot = Some known; _ } as p) when pending e p ->
          changes page (read_page e page) known
      | _ -> [])

(* the changed bytes of the page, which Primus fetches, see [backing],
   after which the page is clean, if it didn't change *)
let fetch_page e page =
  match Hashtbl.find e.pages page with
  | Some ({ snapshot = Some known; _ } as p) when pending e p ->
      let data = read_page e page in
      let changed = changes page data known in
      Bytes.blit ~src:data ~src_pos:0 ~dst:known ~dst_pos:0
        ~len:(Bytes.length data);
      p.fetched <- e.runs;
      if List.is_empty changed then begin
        p.dirty <- false;
        e.dirty <- List.filter e.dirty ~f:(fun x -> Int64.(x <> page));
        Uc.mem_protect e.uc page page_size Uc.Perm.(p.perm - write)
      end;
      changed
  | _ -> []

let parked_changes page { data; copy; unfetched } =
  match copy.snapshot with
  | Some known when unfetched -> changes page data known
  | _ -> []

(* the changed bytes of the parked page, which Primus fetches *)
let fetch_parked page stash =
  let changed = parked_changes page stash in
  (match stash.copy.snapshot with
  | Some known when stash.unfetched ->
      Bytes.blit ~src:stash.data ~src_pos:0 ~dst:known ~dst_pos:0
        ~len:(Bytes.length known)
  | _ -> ());
  stash.unfetched <- false;
  changed

let all_parked_changes pages =
  Hashtbl.fold pages ~init:[] ~f:(fun ~key ~data acc ->
      parked_changes key data @ acc)

(* The memory of Primus, whose pages are in Unicorn, or are parked. The
   bytes of the machine, that runs in Unicorn, are fetched from it, and
   the bytes, that Primus stores, are copied to it, as they are to the
   copied pages. *)
let backing s memory : Primus.Memory.Backing.t =
  let words e =
    List.map ~f:(fun (addr, data) ->
        (Word.of_int64 ~width:(e.bytes * 8) addr, data))
  in
  {
    memory;
    pending =
      (fun id addr ->
        match s.active with
        | None -> false
        | Some e -> (
            let page = page_of (int64_of_word addr) in
            if is_owner e id then
              match Hashtbl.find e.pages page with
              | Some p -> pending e p
              | None -> false
            else
              match Hashtbl.find s.parked id with
              | Some pages -> (
                  match Hashtbl.find pages page with
                  | Some stash -> stash.unfetched
                  | None -> false)
              | None -> false));
    fetch =
      (fun id addr ->
        match s.active with
        | None -> []
        | Some e ->
            let page = page_of (int64_of_word addr) in
            words e
              (if is_owner e id then fetch_page e page
               else
                 match Hashtbl.find s.parked id with
                 | None -> []
                 | Some pages -> (
                     match Hashtbl.find pages page with
                     | Some stash -> fetch_parked page stash
                     | None -> [])));
    fetch_all =
      (fun id ->
        match s.active with
        | None -> []
        | Some e ->
            words e
              (if is_owner e id then List.concat_map e.dirty ~f:(fetch_page e)
               else
                 match Hashtbl.find s.parked id with
                 | Some pages ->
                     Hashtbl.fold pages ~init:[] ~f:(fun ~key ~data acc ->
                         fetch_parked key data @ acc)
                 | None -> []));
    stored =
      (fun id addr data ->
        match s.active with
        | Some e when is_owner e id ->
            let addr = int64_of_word addr in
            let code = ref false in
            String.iteri data ~f:(fun i c ->
                let addr = Int64.(addr + of_int i) in
                (* the copies of the read-only pages too, e.g., of the
                   code, that a script patches, see [Bap_emu.write] *)
                match Hashtbl.find e.pages (page_of addr) with
                | Some { snapshot; perm; _ } ->
                    Option.iter snapshot ~f:(fun known ->
                        Bytes.set known
                          Int64.(to_int_exn (addr - page_of addr))
                          c);
                    Uc.mem_write e.uc addr (String.of_char c);
                    if Uc.Perm.mem perm Uc.Perm.exec then code := true
                | None -> ());
            (* the code, which Unicorn translated, is translated anew *)
            if !code then Uc.flush_tb e.uc
        | _ -> (
            match Hashtbl.find s.parked id with
            | None -> ()
            | Some pages ->
                let addr = int64_of_word addr in
                String.iteri data ~f:(fun i c ->
                    let addr = Int64.(addr + of_int i) in
                    match Hashtbl.find pages (page_of addr) with
                    | Some { data; copy; _ } ->
                        let off = Int64.(to_int_exn (addr - page_of addr)) in
                        Bytes.set data off c;
                        Option.iter copy.snapshot ~f:(fun known ->
                            Bytes.set known off c)
                    | None -> ())));
  }

(* the first write of the code to a writable page, which is read-only
   in Unicorn, until it is dirty *)
let written_page e addr =
  match Hashtbl.find e.pages (page_of addr) with
  | Some ({ snapshot = Some _; dirty = false; perm; _ } as p) ->
      p.dirty <- true;
      e.dirty <- page_of addr :: e.dirty;
      Uc.mem_protect e.uc (page_of addr) page_size perm;
      true
  | _ -> false

(* the number of the bytes from [addr], at most [n], that Primus has
   and may read, which are in Unicorn, raises [Missing] for the first
   address of a page that is not copied yet, see [Native] *)
let uc_readable e addr n =
  if n < 0 then raise Native.Denied;
  let rec count addr n acc =
    if n = 0 then acc
    else
      let page = page_of addr in
      let off = Int64.(to_int_exn (addr - page)) in
      let len = Int.min n (Int64.to_int_exn page_size - off) in
      match Hashtbl.find e.pages page with
      | None -> raise (Native.Missing addr)
      | Some { perm; _ } when not (Uc.Perm.mem perm Uc.Perm.read) -> acc
      | Some { holes; _ } -> (
          let hole =
            List.filter_map holes ~f:(fun (lo, hi) ->
                if hi >= off && lo < off + len then Some (Int.max lo off)
                else None)
            |> List.min_elt ~compare:Int.compare
          in
          match hole with
          | Some first -> acc + first - off
          | None -> count Int64.(addr + of_int len) (n - len) (acc + len))
  in
  count addr n 0

let uc_read e addr n =
  if uc_readable e addr n < n then raise Native.Denied
  else if n = 0 then ""
  else Uc.mem_read e.uc addr n

let uc_prefix e addr n =
  match uc_readable e addr n with 0 -> "" | n -> Uc.mem_read e.uc addr n

let uc_memory e : Native.memory = { read = uc_read e; prefix = uc_prefix e }

(* the bytes may be written by a native function, as Primus may
   write them *)
let uc_check_write e addr n =
  if uc_readable e addr n < n then raise Native.Denied;
  let last = Int64.(addr + of_int n - 1L) in
  let rec check page =
    if Int64.(page <= last) then begin
      (match Hashtbl.find e.pages page with
      | Some { snapshot = Some _; _ } -> ()
      | _ -> raise Native.Denied);
      check Int64.(page + page_size)
    end
  in
  if n > 0 then check (page_of addr)

(* the code, that the native function writes, e.g., memcpy, which
   Unicorn translated, is translated anew, as Unicorn doesn't drop it *)
let uc_write e addr data =
  let n = String.length data in
  if n > 0 then begin
    let last = Int64.(addr + of_int n - 1L) in
    let code = ref false in
    let rec dirty page =
      if Int64.(page <= last) then begin
        ignore (written_page e page : bool);
        Option.iter (Hashtbl.find e.pages page) ~f:(fun p ->
            p.fetched <- -1;
            if Uc.Perm.mem p.perm Uc.Perm.exec then code := true);
        dirty Int64.(page + page_size)
      end
    in
    dirty (page_of addr);
    Uc.mem_write e.uc addr data;
    if !code then Uc.flush_tb e.uc
  end

(* the value of an expression in Unicorn *)
let rec eval_uc e (exp : exp) =
  match exp with
  | Var v -> (
      match Target.Regs.read e.regs v with
      | Some x -> x
      | None -> raise Native.Denied)
  | Int x -> x
  | Cast (kind, n, x) -> Bil.Apply.cast kind n (eval_uc e x)
  | Extract (hi, lo, x) -> Word.extract_exn ~hi ~lo (eval_uc e x)
  | BinOp (((PLUS | MINUS) as op), x, y) ->
      Bil.Apply.binop op (eval_uc e x) (eval_uc e y)
  | Load (_, addr, endian, size) ->
      let addr = int64_of_word (eval_uc e addr) in
      Word.of_binary ~width:(Size.in_bits size) endian
        (uc_read e addr (Size.in_bytes size))
  | _ -> raise Native.Denied

(* writes the result to a register, the result in the lower part of a
   register is sign-extended to the whole register, as the ABIs of
   RISC-V and MIPS64 want for the 32-bit results, and the others leave
   the upper bits undefined *)
let assign_uc e (exp : exp) x =
  match exp with
  | Var v -> Target.Regs.write e.regs v x
  | Cast (LOW, _, Var v) | Extract (_, 0, Var v) -> (
      match Var.typ v with
      | Imm width -> Target.Regs.write e.regs v (Bil.Apply.cast SIGNED width x)
      | _ -> false)
  | _ -> false

(* the return address of the call, which just started, and the stack
   pointer after the return, in Unicorn *)
let frame_uc e =
  let sp = int64_of_word (eval_uc e (Var e.sp)) in
  match e.link with
  | Some lr -> { ret = int64_of_word (eval_uc e (Var lr)); sp }
  | None ->
      (* the return address on the stack of x86 *)
      let ret =
        Word.of_binary ~width:(e.bytes * 8) LittleEndian (uc_read e sp e.bytes)
      in
      { ret = int64_of_word ret; sp = Int64.(sp + of_int e.bytes) }

(* Hooks the events, that the observers see: the instructions, whose
   addresses the observers of the program counter see, and the loads and
   the stores, after which Unicorn stops at the next instruction, so that
   the observers see them synchronously, with the state of the machine in
   Primus, and may change it. The instruction, that runs again, e.g.,
   after its fault, or from the address, at which Unicorn stopped, is not
   observed again, as Unicorn starts anew, see [starts]. *)
(* the write of [size] bytes at [addr] to the code, that the observers,
   which need the writes to the code only, see [watching], see when the
   engine stops, see [Make.observe], as the ranges of the addresses, by
   their pages, merged, so that the program, that writes much code, e.g.,
   a packer, or writes the same code often, e.g., a loop, that patches its
   instruction, keeps as much as the code, that it wrote, rather than its
   writes *)
let code_written e addr size =
  let last = Int64.(addr + of_int size - 1L) in
  let rec pages a =
    let page = page_of a in
    let hi = Int64.min last Int64.(page + page_size - 1L) in
    let ranges = Option.value (Hashtbl.find e.code_written page) ~default:[] in
    let merged, rest =
      List.partition_tf ranges ~f:(fun (lo, hi') ->
          Int64.(lo <= hi + 1L && a <= hi' + 1L))
    in
    let lo = List.fold merged ~init:a ~f:(fun lo (l, _) -> Int64.min lo l)
    and hi = List.fold merged ~init:hi ~f:(fun hi (_, h) -> Int64.max hi h) in
    Hashtbl.set e.code_written ~key:page ~data:((lo, hi) :: rest);
    if Int64.(hi < last) then pages Int64.(page + page_size)
  in
  pages addr

let watch e (w : watching) =
  if not (Poly.equal e.watching w) then begin
    List.iter e.watchers ~f:(Uc.delete e.uc);
    e.watchers <- [];
    e.watching <- w;
    let add hook = e.watchers <- hook :: e.watchers in
    if w.reads then
      add
        (Uc.on_mem e.uc [ `read_after ] (fun _ addr size value ->
             Queue.enqueue e.session.events (Loaded (addr, size, value))));
    let stored _ addr size value =
      Queue.enqueue e.session.events (Stored (addr, size, value))
    in
    if w.writes then add (Uc.on_mem e.uc [ `write ] stored)
    else if w.code_writes then
      (* the writes to the code are seen, when the engine stops, before
         the interpreter runs the code, rather than at once, so that the
         engine isn't stopped at each instruction, see [code_written] *)
      List.iter e.code_segments ~f:(fun (first, last) ->
          add
            (Uc.on_mem ~first ~last e.uc [ `write ] (fun _ addr size _ ->
                 code_written e addr size)));
    if w.pcs || w.reads || w.writes then
      add
        (Uc.on_code e.uc (fun addr _ ->
             if w.pcs || not (Queue.is_empty e.session.events) then
               match e.observed with
               | Some (last, start)
                 when Int64.equal last addr && start <> e.session.starts ->
                   ()
               | _ ->
                   e.observed <- Some (addr, e.session.starts);
                   e.reason <- Some (Observe addr);
                   Uc.stop e.uc));
    (* the hooks of the code apply to the code, that Unicorn translates
       after them *)
    Uc.flush_tb e.uc
  end

(* the entry of the trampoline, whose instructions are at [addr], as
   Unicorn may run the instructions after the entry, which do nothing,
   e.g., when the stop of the hook of the entry is lost, as the timeout
   stops Unicorn too, so that the function is called, and a thread, that
   is preempted there, continues, from the entry, or [addr] *)
let trampoline e addr =
  let base = if e.bytes = 8 then 0x7FFF_FFF0_0000L else 0xFFFF_0000L in
  if Int64.(addr < base) || Hashtbl.mem e.trampolines addr then addr
  else
    let entry =
      Int64.(base + ((addr - base) / trampoline_size * trampoline_size))
    in
    if Hashtbl.mem e.trampolines entry then entry else addr

(* the name of the function at the address, which Unicorn calls *)
let function_name e addr =
  let addr = trampoline e addr in
  match Hashtbl.find e.trampolines addr with
  | Some name -> Some name
  | None -> Hashtbl.find e.session.names addr

(* runs the hooks of the call of the function, the first of which, that
   returns a value, returns it from the call, so that Unicorn continues
   from the return address, which is the result *)
let call_returns e name =
  match Hashtbl.find e.session.call_hooks name with
  | None -> None
  | Some hooks -> (
      match
        List.find_map (List.rev hooks) ~f:(fun hook ->
            match hook () with Return x -> Some x | Default -> None)
      with
      | None -> None
      | Some x ->
          let frame = frame_uc e in
          (match Hashtbl.find e.session.signatures name with
          | Some { output = Some (exp, width); _ } ->
              ignore (assign_uc e exp (Word.of_int64 ~width x) : bool)
          | _ -> ());
          if Option.is_none e.link then
            ignore
              (Target.Regs.write e.regs e.sp
                 (Word.of_int64 ~width:(e.bytes * 8) frame.sp)
                : bool);
          Some frame.ret)

module Make (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  open Machine.Let
  module Env = Primus.Env.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)
  module Value = Primus.Value.Make (Machine)
  module Linker = Primus.Linker.Make (Machine)
  module Interpreter = Primus.Interpreter.Make (Machine)
  module Lisp = Primus.Lisp.Make (Machine)
  module Track = Primus.Track.Make (Machine)
  module Lift = Primus.Lift.Make (Machine)

  let fail fmt = ksprintf (fun msg -> Machine.raise (Unicorn_failure msg)) fmt
  let word e x = Word.of_int64 ~width:(e.bytes * 8) x

  (* the session of the system, see [Loader.init] *)
  let session = Machine.Global.get session_state

  (* The taint, that the lifted engine propagates itself, see
     [Bap_lifted.taint_start], rather than the interpreter, while one
     policy of the taint declares its propagation, see
     [Taint.Propagation.Policy.shadow], and no observer needs the
     interpreter, e.g., of the attached taint, or of its garbage. The
     taint of the registers and of the memory goes to the engine, when
     the taint of Primus changes, see [tracking], or Primus writes the
     registers, see [push_vars], and back to Primus, when it gets the
     registers, see [pull_regs]. The objects of the taint are the labels
     of the engine, by their numbers. BAP_LIFTED_TAINT=false leaves the
     tainted code to the interpreter, as Unicorn does. *)
  module Shadow = struct
    module T = Bap_taint.Std.Taint
    module Tracker = T.Tracker.Make (Machine)
    module Objects = T.Object.Make (Machine)
    module Policy = T.Propagation.Policy.Make (Machine)

    let enabled =
      not
        (Option.equal String.equal
           (Sys.getenv "BAP_LIFTED_TAINT")
           (Some "false"))

    let label o =
      Objects.to_value o >>| fun v -> Word.to_int_exn (Primus.Value.to_word v)

    let labels objs = Machine.List.map (Set.to_list objs) ~f:label

    let objects ls =
      Machine.List.map ls ~f:(fun l ->
          Value.of_word (Word.of_int ~width:63 l) >>= Objects.of_value)
      >>| T.Object.Set.of_list

    (* starts or stops the propagation of the engine *)
    let decide (e : engine) =
      if not (e.session.lifted && enabled) then Machine.return false
      else
        let observed = Machine.Observation.observed in
        let* attached = observed T.attached in
        let* finalized = observed T.Gc.taint_finalize in
        let* jumps = observed Primus.Interpreter.jumping in
        let* opaque = Track.is_opaque in
        let+ shadows = Policy.shadows in
        let on =
          (not attached) && (not finalized) && (not opaque)
          && List.length shadows = 1
        in
        if on then Uc.taint_start ~jumps e.uc
        else begin
          Uc.taint_stop e.uc;
          e.shadowed <- false
        end;
        e.shadowing <- on;
        on

    let classes objs =
      let* shadows = Policy.shadows in
      Machine.List.map (Set.to_list objs) ~f:(fun o ->
          let* kind = Objects.kind o in
          let* l = label o in
          let+ c =
            Machine.List.fold shadows ~init:`None ~f:(fun c (p, c') ->
                match c with
                | `None ->
                    Policy.selected p kind >>| fun selected ->
                    if selected then (c' :> [ `All | `Moves | `None ])
                    else `None
                | c -> Machine.return c)
          in
          (l, c))

    let owner (e : engine) v =
      Option.value (Target.Regs.owner e.regs (Var.name v)) ~default:(Var.name v)

    (* the taint of the register, that Primus wrote, goes to the engine,
       which the register of the basis replaces, and an alias adds *)
    let pushed (e : engine) v =
      let* set = Env.is_set v in
      if not set then Machine.return ()
      else
        let* x = Env.get v in
        let* objs = Tracker.lookup x T.Rel.direct in
        let+ ls = labels objs in
        let r = owner e v in
        if String.equal r (Var.name v) then Uc.set_reg_labels e.uc r ls
        else if not (List.is_empty ls) then
          Uc.set_reg_labels e.uc r
            (List.dedup_and_sort ~compare (Uc.reg_labels e.uc r @ ls))

    (* the taint of Primus goes to the engine, after its changes went to
       Primus, see [export]: of the registers, and of the locations, whose
       taint changed, or of all, if the engine has none, with the classes
       of the labels, that the engine has seen *)
    let import (e : engine) =
      (* the labels of the sets, which the locations share *)
      let sets = Hashtbl.Poly.create () in
      let labels_of objs =
        let key = Set.to_list objs in
        match Hashtbl.find sets key with
        | Some ls -> Machine.return ls
        | None ->
            let+ ls =
              Machine.List.map (Set.to_list objs) ~f:(fun o ->
                  let* l = label o in
                  let+ v = Objects.to_value o in
                  if not (Hashtbl.mem e.known l) then
                    Hashtbl.set e.known ~key:l ~data:v;
                  l)
            in
            Hashtbl.set sets ~key ~data:ls;
            ls
      in
      let* regs =
        Machine.List.filter_map (Target.Regs.vars e.regs) ~f:(fun v ->
            let* set = Env.is_set v in
            if not set then Machine.return None
            else
              let* x = Env.get v in
              let* objs = Tracker.lookup x T.Rel.direct in
              if Set.is_empty objs then Machine.return None
              else
                let+ ls = labels_of objs in
                Some (owner e v, ls))
      in
      let* changes = Tracker.indirect_changes in
      let* full, taints =
        match changes with
        | `Changed taints when e.shadowed -> Machine.return (false, taints)
        | _ ->
            let+ taints = Tracker.indirect_taints in
            (true, taints)
      in
      let* mem =
        Machine.List.map taints ~f:(fun (addr, objs) ->
            let+ ls = labels_of objs in
            (int64_of_word (Primus.Value.to_word addr), ls))
      in
      let* known =
        Machine.List.map (Hashtbl.data e.known) ~f:Objects.of_value
      in
      let+ classes = classes (T.Object.Set.of_list known) in
      Uc.taint_labels e.uc classes;
      Uc.taint_clear ~mem:full e.uc;
      e.shadowed <- true;
      List.iter regs ~f:(fun (r, ls) ->
          Uc.set_reg_labels e.uc r
            (List.dedup_and_sort ~compare (Uc.reg_labels e.uc r @ ls)));
      List.iter mem ~f:(fun (addr, ls) -> Uc.set_mem_labels e.uc addr ls)

    (* the taint, that the engine changed, goes to Primus, to the values
       of the registers, which are new, if their taint changed, as the
       other variables may have the old ones, and to the locations *)
    let export (e : engine) =
      let regs, mem = Uc.taint_changes e.uc in
      let regs =
        List.dedup_and_sort ~compare:String.compare (regs @ Uc.tainted_regs e.uc)
      in
      if List.is_empty regs && List.is_empty mem then Machine.return ()
      else
        let* before = Track.version in
        let* () =
          Machine.List.iter regs ~f:(fun r ->
              match
                List.find e.basis ~f:(fun v -> String.equal (Var.name v) r)
              with
              | None -> Machine.return ()
              | Some v ->
                  let* set = Env.is_set v in
                  if not set then Machine.return ()
                  else
                    let* x = Env.get v in
                    let* have = Tracker.lookup x T.Rel.direct in
                    let* want = objects (Uc.reg_labels e.uc r) in
                    if Set.equal have want then Machine.return ()
                    else
                      let* x = Value.of_word (Primus.Value.to_word x) in
                      let* () = Env.set v x in
                      if Set.is_empty want then Machine.return ()
                      else Tracker.attach x T.Rel.direct want)
        in
        (* the objects of the sets of the labels, which the bytes share *)
        let sets = Hashtbl.Poly.create () in
        let* taints =
          Machine.List.map mem ~f:(fun addr ->
              let* a = Value.of_word (word e addr) in
              let ls = Uc.mem_labels e.uc addr in
              let+ objs =
                match Hashtbl.find sets ls with
                | Some objs -> Machine.return objs
                | None ->
                    let+ objs = objects ls in
                    Hashtbl.set sets ~key:ls ~data:objs;
                    objs
              in
              (a, objs))
        in
        let* () = Tracker.set_indirect taints in
        (* the taint of Primus, that the engine has, is seen *)
        let+ after = Track.version in
        if before = e.seen then e.seen <- after
  end

  (* The intrinsic of the instruction, that interrupts Unicorn at [pc],
     lifted on demand, as the program, e.g., the bare one, may have no IR
     of it, and the interrupts are rare, from the bytes, that [read]
     reads, see [Lift.insn]. The instruction is at [pc], or ends there,
     as Unicorn raises the interrupt, see [raised_at], and returns the
     address, from which Unicorn continues. *)
  let trap ~read ?encoding (arch : Uc.arch) ~thumb n pc =
    let sizes =
      match arch with
      | X86 -> List.range 1 16
      | Arm when thumb -> [ 2; 4 ]
      | _ -> [ 4 ]
    in
    let at () =
      Lift.insn ?encoding ~read pc
      >>| Option.bind ~f:(fun (size, blks) ->
          Option.map (site_of_blocks blks) ~f:(fun site ->
              (site, Int64.(pc + of_int size))))
    and before () =
      (* the instructions, that the disassembler found, go first, as the
         other guesses are lifted anew, see [Lift.insn] *)
      Machine.List.find_map [ true; false ] ~f:(fun disassembled_only ->
          Machine.List.find_map sizes ~f:(fun size ->
              Lift.insn ~disassembled_only ?encoding ~read
                Int64.(pc - of_int size)
              >>| function
              | Some (n, blks) when n = size ->
                  Option.map (site_of_blocks blks) ~f:(fun site -> (site, pc))
              | _ -> None))
    in
    let first f g =
      f () >>= function Some _ as x -> Machine.return x | None -> g ()
    in
    if raised_at arch n then first at before else first before at

  let owns e =
    let+ id = Machine.current () in
    is_owner e id

  (* drops the pages, which are copied anew *)
  let forget e =
    Hashtbl.iter_keys e.pages ~f:(fun page -> Uc.mem_unmap e.uc page page_size);
    Hashtbl.clear e.pages;
    e.unchecked <- [];
    e.dirty <- [];
    e.written <- [];
    Hash_set.clear e.tracked;
    e.clobbered <- [];
    e.seen <- -1

  (* the pages of the owner, which another machine claims, are parked,
     until the owner claims Unicorn again, or the pending ones, if too
     many are parked *)
  let park e =
    let s = e.session in
    Option.iter e.owner ~f:(fun owner ->
        if not (Hash_set.mem s.dead owner) then
          let pages =
            Hashtbl.find_or_add s.parked owner ~default:Int64.Table.create
          in
          Hashtbl.iteri e.pages ~f:(fun ~key:page ~data:copy ->
              let unfetched = pending e copy in
              if unfetched || s.parked_pages < parked_limit then begin
                let data = read_page e page in
                let unfetched =
                  unfetched
                  &&
                  match copy.snapshot with
                  | Some known -> not (Bytes.equal data known)
                  | None -> false
                in
                if not (Hashtbl.mem pages page) then
                  s.parked_pages <- s.parked_pages + 1;
                Hashtbl.set pages ~key:page ~data:{ data; copy; unfetched }
              end))

  (* the parked pages of the machine go to Unicorn, with the pending
     ones writable and dirty *)
  let unpark e id =
    Option.iter (Hashtbl.find e.session.parked id) ~f:(fun pages ->
        unpark_all e.session id;
        Hashtbl.iteri pages ~f:(fun ~key:page ~data:{ data; copy; unfetched } ->
            let perm =
              if unfetched then copy.perm else Uc.Perm.(copy.perm - write)
            in
            Uc.mem_map e.uc page page_size perm;
            Uc.mem_write e.uc page (Bytes.to_string data);
            copy.dirty <- unfetched;
            copy.fetched <- -1;
            if unfetched then e.dirty <- page :: e.dirty;
            (match copy with
            | { snapshot = Some _; holes = _ :: _ as holes; _ } ->
                e.unchecked <- (page, holes) :: e.unchecked
            | _ -> ());
            Hashtbl.set e.pages ~key:page ~data:copy))

  let store_changes e =
    Machine.List.iter ~f:(fun (addr, data) ->
        Memory.store_bytes (word e addr) data)

  (* the pending parked pages of the machine go to its memory *)
  let materialize e id =
    match Hashtbl.find e.session.parked id with
    | None -> Machine.return ()
    | Some pages ->
        store_changes e
          (Hashtbl.fold pages ~init:[] ~f:(fun ~key ~data acc ->
               fetch_parked key data @ acc))

  (* the pages and the registers of another machine are not valid *)
  let claim e =
    let* owned = owns e in
    if owned then Machine.return false
    else
      let+ id = Machine.current () in
      park e;
      forget e;
      e.owner <- Some id;
      unpark e id;
      true

  let union (p : Primus.Memory.protection) (q : Primus.Memory.protection) :
      Primus.Memory.protection =
    {
      readable = p.readable || q.readable;
      writable = p.writable || q.writable;
      executable = p.executable || q.executable;
    }

  (* the page has the access of all its bytes, as Unicorn protects the
     whole pages *)
  let map_page e page =
    let base = word e page in
    let bytes = Bytes.make (Int64.to_int_exn page_size) '\000' in
    let none : Primus.Memory.protection =
      { readable = false; writable = false; executable = false }
    in
    let+ loaded = Memory.load_bytes base (Bytes.length bytes) in
    let holes, access =
      Array.foldi loaded ~init:([], none) ~f:(fun i (holes, access) -> function
        | Some (c, p) ->
            Bytes.set bytes i c;
            (holes, union access p)
        | None -> (
            match holes with
            | (first, last) :: holes when last + 1 = i ->
                ((first, i) :: holes, access)
            | holes -> ((i, i) :: holes, access)))
    in
    let writable = access.writable in
    List.iter (Hashtbl.find_multi e.slots page) ~f:(fun (off, addr) ->
        if off + e.bytes <= Bytes.length bytes then
          List.iteri (List.init e.bytes ~f:Fn.id) ~f:(fun i _ ->
              let shift = if e.big_endian then e.bytes - 1 - i else i in
              let byte =
                Int64.(shift_right_logical addr Int.(8 * shift) land 0xFFL)
              in
              Bytes.set bytes (off + i)
                (Char.of_int_exn (Int64.to_int_exn byte))));
    let data = Bytes.to_string bytes in
    let perm =
      Uc.Perm.(
        (if access.readable then read else none)
        + (if writable then write else none)
        + if access.executable then exec else none)
    in
    Uc.mem_map e.uc page page_size Uc.Perm.(perm - write);
    Uc.mem_write e.uc page data;
    Hashtbl.set e.pages ~key:page
      ~data:
        {
          snapshot = (if writable then Some (Bytes.of_string data) else None);
          holes;
          perm;
          dirty = false;
          fetched = 0;
        }

  (* the page, that has a tracked location, unless the engine propagates
     the taint, see [Shadow] *)
  let marked_page e addr =
    if e.shadowing then Machine.return false
    else Track.page_marked (word e addr)

  (* the page, which has a tracked location, stays in Primus, so that
     the code, which accesses it, faults, and is interpreted *)
  let ensure_page e addr =
    let page = page_of addr in
    if Hashtbl.mem e.pages page then Machine.return ()
    else
      let* mapped = Memory.is_mapped (word e addr) in
      let* marked = marked_page e addr in
      if mapped && not marked then map_page e page else Machine.return ()

  (* maps the code, so that it is never fetched from unmapped pages,
     see [broken] *)
  let map_code e =
    match e.arch with
    | Mips ->
        let* memory = Machine.gets Project.memory in
        Memmap.to_sequence memory
        |> Seq.filter_map ~f:(fun (mem, tag) ->
            match Bap.Std.Value.get Image.segment tag with
            | Some seg when Image.Segment.is_executable seg -> Some mem
            | _ -> None)
        |> Seq.to_list
        |> Machine.List.iter ~f:(fun mem ->
            let first = page_of (int64_of_word (Bap.Std.Memory.min_addr mem)) in
            let last = int64_of_word (Bap.Std.Memory.max_addr mem) in
            let pages =
              List.init
                (Int64.to_int_exn Int64.((last - first) / page_size) + 1)
                ~f:(fun i -> Int64.(first + (of_int i * page_size)))
            in
            Machine.List.iter pages ~f:(ensure_page e))
    | _ -> Machine.return ()

  (* copies the registers that changed in Unicorn to Primus, and the
     tracked ones, that it wrote, see [trace], which are not tracked
     anymore *)
  let pull_regs e =
    let clobbered = e.clobbered in
    e.clobbered <- [];
    Machine.List.iter e.basis ~f:(fun v ->
        match Target.Regs.read e.regs v with
        | Some x
          when List.mem clobbered (Var.name v) ~equal:String.equal
               || not
                    (Option.equal Word.equal
                       (Hashtbl.find e.synced (Var.name v))
                       (Some x)) ->
            Hashtbl.set e.synced ~key:(Var.name v) ~data:x;
            Hash_set.remove e.tracked (Var.name v);
            Value.of_word x >>= Env.set v
        | _ -> Machine.return ())
    >>= fun () -> if e.shadowing then Shadow.export e else Machine.return ()

  (* copies the registers from Primus, the aliases go first, so that
     the registers of the program win, and then the registers, which the
     aliases changed, go back to Primus *)
  let push_vars e vars =
    (* the bases of the segments of x86 in the protected mode are in its
       descriptors, see [Target.Segments] *)
    let* () =
      if Poly.(e.arch = Uc.X86) && e.bytes = 4 then
        Machine.List.iter vars ~f:(fun v ->
            if Target.Segments.is_base (Var.name v) then
              let+ x = Env.get v in
              ignore
                (Target.Segments.set e.uc (Var.name v)
                   (Bitvec.to_int64 (Word.to_bitvec (Primus.Value.to_word x)))
                  : bool)
            else Machine.return ())
      else Machine.return ()
    in
    let vars = List.filter vars ~f:(Target.Regs.mem e.regs) in
    let is_basis v = List.mem e.basis v ~equal:Var.equal in
    let aliases, basis = List.partition_tf vars ~f:(Fn.non is_basis) in
    let* () =
      Machine.List.iter (aliases @ basis) ~f:(fun v ->
          let+ x = Env.get v in
          let x = Primus.Value.to_word x in
          if Target.Regs.write e.regs v x && is_basis v then
            Hashtbl.set e.synced ~key:(Var.name v) ~data:x)
    in
    let* () =
      if e.shadowing then
        Machine.List.iter (aliases @ basis) ~f:(Shadow.pushed e)
      else Machine.return ()
    in
    e.written <- [];
    (* the registers, which the aliases changed, e.g., the flags in a
       status register, go back to Primus *)
    if List.is_empty aliases then Machine.return () else pull_regs e

  (* copies all registers from Primus, that are set, as the others are
     generated, when they are read, e.g., as the symbolic inputs *)
  let push e =
    Hashtbl.clear e.synced;
    let* vars = Env.all in
    let* vars = Machine.List.filter (Seq.to_list vars) ~f:Env.is_set in
    push_vars e vars

  (* the values of the registers, that are set in Primus *)
  let registers e =
    Target.Regs.vars e.regs
    |> Machine.List.filter_map ~f:(fun v ->
        Env.is_set v >>= function
        | false -> Machine.return None
        | true ->
            let+ x = Env.get v in
            Some (v, Primus.Value.to_word x))
    >>| Var.Map.of_alist_reduce ~f:(fun _ x -> x)

  (* copies the registers that Primus has written *)
  let push_written e = push_vars e (List.rev e.written)

  (* the registers that Primus has written go to Unicorn, unless another
     machine has run in it, as then all registers go there, see [loop] *)
  let push_owned e =
    let* owned = owns e in
    if owned then push_written e else Machine.return ()

  (* the registers, that Primus writes, go to Unicorn, and they are
     tracked, if their values are, see [trace] *)
  let written (v, x) =
    let* s = session in
    match s.active with
    | Some e when Target.Regs.mem e.regs v -> (
        e.written <- v :: e.written;
        match Target.Regs.owner e.regs (Var.name v) with
        | None -> Machine.return ()
        | Some r ->
            let+ tracked = Track.is_tracked x in
            if tracked && not e.shadowing then Hash_set.add e.tracked r
            else if String.equal r (Var.name v) then Hash_set.remove e.tracked r
        )
    | _ -> Machine.return ()

  (* copies the pending page to Primus *)
  let sync_page e page = store_changes e (fetch_page e page)

  (* copies the pending pages to Primus *)
  let sync e = Machine.List.iter e.dirty ~f:(sync_page e)

  (* copies the registers to Primus, the dirty pages are fetched, when
     Primus accesses them, and checks the writable pages, that Primus
     may extend, see [page] *)
  let pull e =
    let+ () = pull_regs e in
    (* a page, which Primus may change, is checked before Unicorn runs *)
    e.unchecked <-
      Hashtbl.fold e.pages ~init:e.unchecked ~f:(fun ~key ~data acc ->
          match data with
          | { snapshot = Some _; holes = _ :: _ as holes; _ } ->
              (key, holes) :: acc
          | _ -> acc)

  (* drops the pages, in which Primus has allocated memory, see [page] *)
  let check_pages e =
    let pages = e.unchecked in
    e.unchecked <- [];
    Machine.List.iter pages ~f:(fun (page, holes) ->
        let* allocated =
          Machine.List.exists holes ~f:(fun (first, last) ->
              let* first =
                Memory.is_mapped (word e Int64.(page + of_int first))
              in
              let+ last =
                Memory.is_mapped (word e Int64.(page + of_int last))
              in
              first || last)
        in
        if allocated && Hashtbl.mem e.pages page then begin
          let+ () = sync_page e page in
          Uc.mem_unmap e.uc page page_size;
          Hashtbl.remove e.pages page
        end
        else Machine.return ())

  (* the pages, whose protection changes, are copied anew, after their
     changes go to Primus *)
  let rec protected (lower, upper, _) = drop lower upper

  (* the page, which has a tracked location, goes to Primus, see
     [ensure_page] *)
  and marked addr =
    let* s = session in
    match s.active with
    | Some e when e.shadowing -> Machine.return ()
    | _ -> drop addr addr

  and drop lower upper =
    let* s = session in
    match s.active with
    | None -> Machine.return ()
    | Some e -> (
        let first = page_of (int64_of_word lower)
        and last = page_of (int64_of_word upper) in
        let inside page =
          Int64.(page >= first && page <= last)
          || Int64.(first > last && (page >= first || page <= last))
        in
        let* id = Machine.current () in
        if is_owner e id then
          let pages = Hashtbl.keys e.pages |> List.filter ~f:inside in
          Machine.List.iter pages ~f:(fun page ->
              let+ () = sync_page e page in
              Uc.mem_unmap e.uc page page_size;
              Hashtbl.remove e.pages page)
        else
          match Hashtbl.find s.parked id with
          | None -> Machine.return ()
          | Some pages ->
              Hashtbl.keys pages |> List.filter ~f:inside
              |> Machine.List.iter ~f:(fun page ->
                  match Hashtbl.find_and_remove pages page with
                  | Some stash ->
                      s.parked_pages <- s.parked_pages - 1;
                      store_changes e (parked_changes page stash)
                  | None -> Machine.return ()))

  (* the fork has the bytes, that its parent has in Unicorn, or parked *)
  let forked (parent, _) =
    let* s = session in
    match s.active with
    | None -> Machine.return ()
    | Some e ->
        store_changes e
          (if is_owner e parent then pending_changes e
           else
             match Hashtbl.find s.parked parent with
             | Some pages -> all_parked_changes pages
             | None -> [])

  let killed id =
    let+ s = session in
    unpark_all s id;
    Hash_set.add s.dead id

  (* the memory of the machine, that finishes the system, is in Primus *)
  let finished () =
    let* s = session in
    match s.active with
    | None -> Machine.return ()
    | Some e ->
        let* id = Machine.current () in
        if is_owner e id then sync e else materialize e id

  let system_stopped _ =
    let* s = session in
    Hashtbl.clear s.parked;
    s.parked_pages <- 0;
    Memory.set_backing None

  (* the engine, which is created anew, if it is broken, after its
     registers go to Primus, and its pages are parked *)
  let engine () =
    let* s = session in
    match (s.active, s.recipe) with
    | Some e, Some (target, foreign, externals) when e.broken ->
        let* owned = owns e in
        let* () = if owned then pull e else Machine.return () in
        (* the pages go to the new engine, when their machine claims it *)
        park e;
        Uc.close e.uc;
        let e = create s target ~foreign ~externals in
        s.active <- Some e;
        Machine.return e
    | Some e, _ -> Machine.return e
    | None, _ -> fail "the engine is not initialized"

  let load_word e addr =
    let+ bytes =
      Machine.List.map (List.init e.bytes ~f:Fn.id) ~f:(fun i ->
          Memory.load Word.(addr ++ i))
    in
    (* the order of the bytes of the return address on x86 *)
    List.fold (List.rev bytes) ~init:0L ~f:(fun acc b ->
        Int64.((acc lsl 8) lor int64_of_word b))

  (* the return address of the call that just started and the stack
     pointer after the return *)
  let frame e =
    let* sp = Env.get e.sp in
    let sp = Primus.Value.to_word sp in
    match e.link with
    | Some lr ->
        let+ ret = Env.get lr in
        {
          ret = int64_of_word (Primus.Value.to_word ret);
          sp = int64_of_word sp;
        }
    | None ->
        let+ ret = load_word e sp in
        { ret; sp = Int64.(int64_of_word sp + of_int e.bytes) }

  (* the address of the code at which Unicorn starts, which on ARM marks
     the Thumb code with the lower bit *)
  let address e { ret; _ } =
    match e.arch with Arm -> Int64.(ret land lnot 1L) | _ -> ret

  let drop_page e page =
    if Hashtbl.mem e.pages page then (
      Uc.mem_unmap e.uc page page_size;
      Hashtbl.remove e.pages page)

  (* repeats the access, that Unicorn denied, in Primus, which signals
     the pagefault trap, as the interpreter does, and raises the
     segmentation fault, unless the pagefault handler fixes the access,
     after which the page is copied anew *)
  let repeat e access addr =
    let a = word e addr in
    let* () = pull e in
    let* v = Value.of_word a in
    let* () =
      match (access : Uc.access) with
      | Write_unmapped | Write_prot ->
          let* x =
            Memory.protection a >>= function
            | Some p when p.readable -> Memory.get a
            | _ -> Value.zero 8
          in
          Interpreter.store v x LittleEndian `r8
      | Fetch_unmapped | Fetch_prot ->
          (* Primus doesn't fetch the code, so it checks only the access *)
          let* _ = Interpreter.load v LittleEndian `r8 in
          let* executable = Memory.is_executable a in
          if executable then Machine.return ()
          else Machine.raise (Primus.Interpreter.Segmentation_fault a)
      | _ -> Interpreter.load v LittleEndian `r8 >>| ignore
    in
    let+ () = sync_page e (page_of addr) in
    drop_page e (page_of addr);
    `Continue

  let fault e access addr =
    match (access : Uc.access) with
    | Write_prot when written_page e addr -> Machine.return `Continue
    | Read_unmapped | Write_unmapped | Fetch_unmapped ->
        let* mapped = Memory.is_mapped (word e addr) in
        let* marked = marked_page e addr in
        if mapped && marked then Machine.return `Interpret
        else if mapped then map_page e (page_of addr) >>| fun () -> `Continue
        else repeat e access addr
    | Read_prot | Write_prot | Fetch_prot -> repeat e access addr
    | Read | Write | Fetch | Read_after ->
        pull e >>= fun () -> fail "access to %Lx is denied" addr

  (* the interpreted stub, if the function is linked to the stub of the
     program, which nothing replaced *)
  let unreplaced_stub e name =
    let* code = Linker.lookup name in
    let+ addr = Linker.resolve_addr name in
    match (code, addr) with
    | Some code, Some addr -> (
        match
          ( Hashtbl.find e.session.own_code addr,
            Hashtbl.find e.session.stubs addr )
        with
        | Some own, Some stub when phys_equal own code -> Some stub
        | _ -> None)
    | _ -> None

  (* the registers of the expressions are tracked, see [trace] *)
  let reads_tracked e exps =
    (not (Hash_set.is_empty e.tracked))
    && List.exists exps ~f:(fun x ->
        Set.exists (Exp.free_vars x) ~f:(fun v ->
            match Target.Regs.owner e.regs (Var.name v) with
            | Some r -> Hash_set.mem e.tracked r
            | None -> false))

  (* runs the native function at the address, unless the code at the
     address is stopped at, the loads or the stores are observed, the
     function is linked to the stub of the program, which nothing
     replaced, or Lisp advises the function, and
     returns the address, from
     which Unicorn continues, or [None], if the function can't run, e.g.,
     when it would fault, so that the stub runs, as the faults are of
     Primus *)
  (* the taint of the native function, as its Lisp stub propagates it,
     which writes the taint of its writes, and of its result, or [None],
     if the function can't run, as it computes its result from the
     tainted bytes or arguments, e.g., memcmp, see [Shadow]; the loops of
     the stubs make no jumps of the interpreter, which the observers see *)
  let native_taint e (call : native) (r : Native.result) reads =
    let owner name =
      Option.value (Target.Regs.owner e.regs name) ~default:name
    in
    let rec taint_of = function
      | Bil.Var v -> Some (Uc.reg_taint e.uc (owner (Var.name v)))
      | Cast (_, _, x) | Extract (_, _, x) ->
          Option.map (taint_of x) ~f:(Uc.moves_taint e.uc)
      | Load (_, addr, _, size) -> (
          match eval_uc e addr with
          | a ->
              Some
                (Uc.mem_range_taint e.uc (int64_of_word a) (Size.in_bytes size))
          | exception (Native.Missing _ | Native.Denied) -> None)
      | _ -> None
    in
    match Option.all (List.map call.args ~f:taint_of) with
    | None -> None
    | Some args ->
        let tainted = List.exists args ~f:Uc.tainted in
        let read =
          List.exists reads ~f:(fun (addr, n) ->
              Uc.tainted (Uc.mem_range_taint e.uc addr n))
        in
        if Option.is_none r.taints && (tainted || read) then None
        else
          Some
            (fun () ->
              Option.iter r.taints ~f:(fun taints ->
                  List.iter taints ~f:(function
                    | Native.Copy { dst; src; n } ->
                        Uc.copy_mem_taint e.uc ~dst ~src n
                    | Move { dst; src; n } -> Uc.move_mem_taint e.uc ~dst ~src n
                    | Fill { dst; n; arg } ->
                        Uc.fill_mem_taint e.uc dst n
                          (Option.value (List.nth args arg) ~default:Uc.no_taint)
                    | Clean { dst; n } ->
                        Uc.fill_mem_taint e.uc dst n Uc.no_taint));
              (* the result is the argument, or isn't tainted *)
              Option.iter call.result ~f:(fun (exp, _) ->
                  match exp with
                  | Bil.Var v | Cast (_, _, Var v) | Extract (_, _, Var v) ->
                      Uc.set_reg_taint e.uc
                        (owner (Var.name v))
                        (Option.value_map r.returns ~default:Uc.no_taint
                           ~f:(fun i ->
                             Option.value (List.nth args i) ~default:Uc.no_taint))
                  | _ -> ()))

  let native e addr =
    let name =
      match Hashtbl.find e.trampolines addr with
      | Some name -> Some name
      | None -> Hashtbl.find e.session.names addr
    in
    match
      Option.bind name ~f:(fun name ->
          Option.map (Hashtbl.find e.session.natives name) ~f:(fun call ->
              (name, call)))
    with
    | None -> Machine.return None
    | Some _ when is_stop e addr -> Machine.return None
    (* the native functions access the memory without its events *)
    | Some _ when e.watching.reads || e.watching.writes -> Machine.return None
    (* the native functions compute the concrete values *)
    | Some (_, call) when reads_tracked e call.args -> Machine.return None
    | Some (name, call) ->
        let* linked = Linker.is_linked (`symbol name) in
        let* unreplaced = unreplaced_stub e (`symbol name) in
        let* advised = Lisp.advised name in
        if (not linked) || Option.is_some unreplaced || advised then
          Machine.return None
        else
          (* the taint, that the lifted engine propagates, see
             [native_taint] *)
          let shadow = e.shadowing && Uc.taint_any e.uc in
          let rec attempt tries =
            match
              let args = List.map call.args ~f:(eval_uc e) in
              let frame = frame_uc e in
              let reads = ref [] in
              let memory : Native.memory =
                {
                  read =
                    (fun addr n ->
                      reads := (addr, n) :: !reads;
                      uc_read e addr n);
                  prefix =
                    (fun addr n ->
                      let data = uc_prefix e addr n in
                      reads := (addr, String.length data) :: !reads;
                      data);
                }
              in
              let r = call.fn memory (List.map args ~f:int64_of_word) in
              List.iter r.writes ~f:(fun (addr, data) ->
                  uc_check_write e addr (String.length data));
              let taint =
                if not shadow then ignore
                else
                  match native_taint e call r !reads with
                  | Some taint -> taint
                  | None -> raise Native.Denied
              in
              (args, frame, r, taint)
            with
            | exception Native.Missing addr when tries > 0 ->
                let* () = ensure_page e addr in
                if Hashtbl.mem e.pages (page_of addr) then attempt (tries - 1)
                else Machine.return None
            | exception (Native.Missing _ | Native.Denied) ->
                Machine.return None
            | args, frame, r, taint ->
                let* () =
                  Machine.Observation.post Primus.Linker.Trace.call_entered
                    ~f:(fun notify ->
                      let* args = Machine.List.map args ~f:Value.of_word in
                      notify (name, args))
                in
                List.iter r.writes ~f:(fun (addr, data) ->
                    uc_write e addr data;
                    (* the writes to the code are seen, see [watch] *)
                    if e.watching.code_writes then
                      let last =
                        Int64.(addr + of_int (String.length data) - 1L)
                      in
                      if
                        List.exists e.code_segments ~f:(fun (first, l) ->
                            Int64.(first <= last && addr <= l))
                      then code_written e addr (String.length data));
                let result =
                  Option.map call.result ~f:(fun (exp, width) ->
                      let x = Word.of_int64 ~width r.value in
                      ignore (assign_uc e exp x : bool);
                      x)
                in
                taint ();
                if Option.is_none e.link then
                  ignore
                    (Target.Regs.write e.regs e.sp (word e frame.sp) : bool);
                let+ () =
                  Machine.Observation.post Primus.Linker.Trace.call_returned
                    ~f:(fun notify ->
                      let* args =
                        Machine.List.map
                          (args @ Option.to_list result)
                          ~f:Value.of_word
                      in
                      notify (name, args))
                in
                Some frame.ret
          in
          attempt 64

  (* the stub of the program, which runs in Unicorn, would jump back to
     the trampoline, so it is interpreted, as load-binary does, which
     calls the function, that nothing defines, by its address *)
  let call_foreign e addr =
    let* () = pull e in
    let* frame =
      match frame_uc e with
      | frame -> Machine.return frame
      | exception (Native.Missing _ | Native.Denied) -> frame e
    in
    let name =
      match Hashtbl.find e.trampolines addr with
      | Some name -> `symbol name
      | None -> `addr (word e addr)
    in

    (* the code that Primus runs instead stops at its address *)
    let* () =
      if (not (Hashtbl.mem e.trampolines addr)) && is_stop e addr then
        Interpreter.set_pc (word e addr)
      else Machine.return ()
    in
    let* () =
      unreplaced_stub e name >>= function
      | Some (module Stub : Primus.Linker.Code) ->
          let module Stub = Stub (Machine) in
          Stub.exec
      | None -> Linker.exec name
    in
    let* () = push_owned e in
    (* the return address is popped on x86, if the stub did not *)
    if Option.is_none e.link then
      ignore (Target.Regs.write e.regs e.sp (word e frame.sp));
    Machine.return frame.ret

  let cpsr = lazy (Option.value_exn (Uc.reg Arm "CPSR"))

  (* the address, from which Unicorn continues, with the lower bit set in
     the Thumb state of ARM *)
  let current_pc e =
    let pc = Uc.reg_read e.uc e.pc in
    match e.arch with
    | Arm ->
        if Int64.(Uc.reg_read e.uc (force cpsr) land 0x20L <> 0L) then
          Int64.(pc lor 1L)
        else pc
    | _ -> pc

  (* the encoding of the mode of ARM, that Unicorn runs, see [Lift.insn] *)
  let arm_encoding (e : engine) ~thumb =
    match e.arch with Arm -> Primus.Interworking.encoding ~thumb | _ -> None

  (* the address of the code in the Thumb state of ARM, see [current_pc] *)
  let in_thumb (e : engine) pc =
    match e.arch with Arm -> Int64.(pc land 1L = 1L) | _ -> false

  (* the address of the instruction at [pc] *)
  let code_addr e pc =
    match e.arch with Arm -> Int64.(pc land lnot 1L) | _ -> pc

  let call_intrinsic e { name; inputs; outputs } =
    let* () = pull e in
    let* () =
      Machine.List.iter inputs ~f:(fun (var, exp) ->
          Interpreter.exp exp >>= Interpreter.set var)
    in
    let* () = Linker.exec (`symbol name) in
    (* the results go to their registers, e.g., of RDTSC, or of the
       counters of RISC-V, which Unicorn doesn't have *)
    let* () =
      Machine.List.iter outputs ~f:(fun (var, exp) ->
          Interpreter.exp exp >>= Interpreter.set var)
    in
    push_owned e

  (* saves the state of the machine, which is in Primus, after it is
     copied from Unicorn, and the innermost run, from which Unicorn
     continues, to the file, or the error *)
  let save e pc file =
    let* () = pull e in
    let* target = Machine.gets Project.target in
    let* vars = Env.all in
    let* vars =
      Seq.to_list vars
      |> List.dedup_and_sort ~compare:Var.compare
      |> Machine.List.filter ~f:Env.is_set
    in
    let* vars =
      Machine.List.map vars ~f:(fun v ->
          let+ x = Env.get v in
          (v, Primus.Value.to_word x))
    in
    let* memory = Memory.snapshot in
    let* extensions =
      Primus.Checkpoint.names ()
      |> Machine.List.filter_map ~f:(fun name ->
          match Primus.Checkpoint.find name with
          | None -> Machine.return None
          | Some (module Ext) ->
              let module Ext = Ext (Machine) in
              let+ data = Ext.save in
              Option.map data ~f:(fun data -> (name, data)))
    in
    let* pending = Machine.Local.get frames in
    let* called = Machine.Local.get calls in
    let* threads = Machine.Local.get threads in
    let+ digest =
      Machine.gets (fun proj -> Project.get proj filename) >>| function
      | None -> ""
      | Some file -> ( try Checkpoint.digest file with Sys_error _ -> "")
    in
    let frames =
      List.mapi pending ~f:(fun i { ret; sp } ->
          let callee, caller =
            Option.value (List.nth called i) ~default:(None, None)
          in
          { Checkpoint.ret; sp; callee; caller })
    in
    let saved =
      match frames with
      | [] -> Error (sprintf "%Lx is outside of a run" pc)
      | _
        when (not (List.is_empty threads.others))
             && not
                  (Option.equal Int.equal threads.depth
                     (Some (List.length pending))) ->
          Error "a thread runs a function of the program, that a stub called"
      | frames ->
          Checkpoint.save file
            {
              target = Theory.Target.to_string target;
              digest;
              pc;
              frames;
              vars;
              memory;
              symbols =
                Hashtbl.to_alist e.session.symbols
                |> List.map ~f:(fun (addr, name) -> (name, addr));
              unstubbed = Hash_set.to_list e.session.unstubbed;
              extensions;
              extra =
                List.map (extra_regs e) ~f:(fun id -> (id, read_extra e id));
              threads =
                (if threads.last = 1 then None
                 else
                   Some
                     {
                       current = threads.current;
                       cleared = threads.cleared;
                       last = threads.last;
                       woken = threads.woken;
                       others =
                         List.map threads.others
                           ~f:(fun
                               { tid; saved_extra; next; wait; clear; woken } ->
                             {
                               Checkpoint.tid;
                               extra = saved_extra;
                               next;
                               clear;
                               woken;
                               waiting =
                                 (match wait with
                                 | Ready -> None
                                 | Waiting addrs -> Some addrs);
                             });
                     });
            }
    in
    Result.iter saved ~f:(fun () ->
        info "saved the checkpoint at %Lx to %s" pc file);
    Result.map_error saved ~f:(sprintf "can't save the checkpoint: %s")

  (* the function of the program at the address runs in Unicorn again,
     instead of the stub, that replaced it, e.g., in Lisp, so that the
     code, that the script patched, runs, see [Bap_emu.unstub] *)
  let unstub addr =
    let* s = session in
    match
      Hashtbl.to_alist s.own_code
      |> List.find ~f:(fun (a, _) -> Int64.equal (int64_of_word a) addr)
    with
    | None -> Machine.return ()
    | Some (a, code) ->
        let* name = Linker.resolve_symbol (`addr a) in
        let* tid = Linker.resolve_tid (`addr a) in
        Hash_set.add s.unstubbed addr;
        Option.iter s.active ~f:(fun e -> Hash_set.remove e.foreign addr);
        s.recipe <-
          Option.map s.recipe ~f:(fun (target, foreign, externals) ->
              ( target,
                List.filter foreign ~f:(fun a -> not (Int64.equal a addr)),
                externals ));
        Linker.link ~addr:a ?name ?tid code

  (* the time since it was last accounted for goes to the machine that
     runs, which is the machine that spent it, as they switch rarely,
     only if the time is limited, as the time is not free to get *)
  let account () =
    let* s = session in
    match s.timeout with
    | None -> Machine.return ()
    | Some _ ->
        let now = clock () in
        let spent = now -. s.accounted in
        s.accounted <- now;
        Machine.Local.update elapsed ~f:(fun t -> t +. spent)

  let halt () =
    let* s = session in
    let* id = Machine.current () in
    info "terminating machine %a, which has run for %g seconds" Id.pp id
      (Option.value_exn s.timeout);
    Interpreter.halt >>= never_returns

  let terminate e =
    let* () = pull e in
    halt ()

  (* the time of the code that Primus runs, e.g., of the Lisp stubs, is
     checked every few thousand ticks of its clock, as the time is not
     free to get *)
  let clocked _ =
    let* s = session in
    match s.timeout with
    | None -> Machine.return ()
    | Some limit ->
        s.ticks <- s.ticks + 1;
        if s.ticks < 4096 then Machine.return ()
        else begin
          s.ticks <- 0;
          let* () = account () in
          let* used = Machine.Local.get elapsed in
          if Float.(used >= limit) then halt () else Machine.return ()
        end

  (* stops Unicorn at the return address of the innermost run *)
  let ensure_return e ret =
    if not (Hashtbl.mem e.returns ret) then (
      Hashtbl.set e.returns ~key:ret ~data:();
      ignore
      @@ Uc.on_code e.uc ~first:ret ~last:ret (fun _ _ ->
          match e.frames with
          | top :: _ when Int64.(top.ret = ret) -> (
              match Target.Regs.read e.regs e.sp with
              | Some sp when Int64.(int64_of_word sp = top.sp) ->
                  e.reason <- Some Returned;
                  Uc.stop e.uc
              | _ -> ())
          | _ -> ()))

  (* the engine may be created anew, see [broken], and another machine
     may have run in it, see [claim] *)
  let prepare () =
    let* e = engine () in
    let* claimed = claim e in
    let* () =
      if claimed then map_code e >>= fun () -> push e else Machine.return ()
    in
    let+ pending = Machine.Local.get frames in
    e.frames <- pending;
    (match pending with top :: _ -> ensure_return e top.ret | [] -> ());
    e

  (* runs Unicorn from [pc], and runs it again after the first writes of
     the pages, see [written_page], which are frequent, so they don't go
     through [loop]; the stop at the instruction, which wrote, is skipped
     again, as in [loop] *)
  let rec start_uc ?count e pc deadline =
    let s = e.session in
    e.reason <- None;
    s.skipped_at <- None;
    s.starts <- s.starts + 1;
    s.restarted_at <-
      (if Option.equal Int64.equal s.stopped_at (Some (code_addr e pc)) then
         s.stopped_at
       else None);
    let error =
      try
        Uc.start e.uc pc ?count
          ?timeout:
            (Option.map deadline ~f:(fun t ->
                 Int.max 1 (Float.iround_up_exn ((t -. clock ()) *. 1e6))));
        None
      with Uc.Error (_, msg) -> Some msg
    in
    e.runs <- e.runs + 1;
    s.stopped_at <- Some (code_addr e (current_pc e));
    (* the handlers of the signals run, e.g., of the script, which may
       pause the program, and else it continues *)
    if Uc.interrupted () then begin
      Uc.process_signals ();
      if Option.is_none e.reason then e.reason <- Some Interrupted
    end;
    match e.reason with
    | Some (Fault (Write_prot, addr)) when written_page e addr ->
        let pc = current_pc e in
        if Option.equal Int64.equal s.skipped_at (Some (code_addr e pc)) then
          s.resumed_at <- s.skipped_at;
        start_uc ?count e pc deadline
    | _ -> error

  (* the stops of the system, which the hooks see, see [is_stop], and
     hook, see [sync_stops] *)
  let sync_stops e =
    let module Stops = Primus.Interpreter.Stops.Make (Machine) in
    let s = e.session in
    let* version = Stops.version in
    let+ () =
      if version = s.stops_seen then Machine.return ()
      else
        let* addrs = Stops.to_list in
        let+ stepping = Stops.stepping in
        s.stops_seen <- version;
        s.stepping <- stepping;
        Hash_set.clear s.stop_addrs;
        List.iter addrs ~f:(fun addr ->
            Hash_set.add s.stop_addrs (int64_of_word addr))
    in
    sync_stops e

  (* the events, that the observers of the machine see, see [watch] *)
  let watching e =
    let observed = Machine.Observation.observed in
    (* the observers of the program counter, e.g., the analyses of
       Lisp, see it at every instruction, but the observers of the stops,
       e.g., a debugger, see it only at the stops, see [sync_stops] and
       [Primus.Interpreter.stop_reached] *)
    let* pcs = observed Primus.Interpreter.pc_change in
    let* loading = observed Primus.Interpreter.loading in
    let* storing = observed Primus.Interpreter.storing in
    (* the observers of the loads and the stores, that need only the
       tracked values, e.g., of the taint, see them in the interpreter,
       which runs the code, that uses them, see [Primus.Track.cover] *)
    let* loaded = Track.uncovered Primus.Interpreter.loaded in
    let* stored = Track.uncovered Primus.Interpreter.stored in
    (* the observers of the stores to the code, e.g., the dynamic code,
       see them only, see [Primus.Track.cover_code] *)
    let* code_writes = Track.code_covered Primus.Interpreter.stored in
    let+ () =
      if code_writes && List.is_empty e.code_segments then
        let+ memory = Machine.gets Project.memory in
        e.code_segments <-
          Memmap.to_sequence memory
          |> Seq.filter_map ~f:(fun (mem, tag) ->
              match Bap.Std.Value.get Image.segment tag with
              | Some seg when Image.Segment.is_executable seg ->
                  Some
                    ( int64_of_word (Bap.Std.Memory.min_addr mem),
                      int64_of_word (Bap.Std.Memory.max_addr mem) )
              | _ -> None)
          |> Seq.to_list
      else Machine.return ()
    in
    watch e
      {
        pcs;
        reads = loading || loaded;
        writes = storing || stored;
        code_writes;
      }

  (* the loads and the stores of the code, that Unicorn ran, which the
     observers see byte by byte, as they see those of Primus, and the
     writes to the code, see [code_written], whose bytes they see, as
     they are now, in the order of their addresses *)
  let observe e =
    let events = e.session.events in
    if Queue.is_empty events && Hashtbl.is_empty e.code_written then
      Machine.return ()
    else
      let happened = Queue.to_list events in
      Queue.clear events;
      let written =
        Hashtbl.data e.code_written
        |> List.concat
        |> List.sort ~compare:(fun (a, _) (b, _) -> Int64.compare a b)
      in
      Hashtbl.clear e.code_written;
      let* () = pull e in
      let bytes addr size value =
        List.init size ~f:(fun i ->
            let shift = if e.big_endian then size - 1 - i else i in
            ( word e Int64.(addr + of_int i),
              Word.of_int64 ~width:8
                Int64.(shift_right_logical value Int.(8 * shift) land 0xFFL) ))
      in
      let* () =
        Machine.List.iter happened ~f:(fun event ->
            let notify, addr, size, value =
              match event with
              | Loaded (addr, size, value) ->
                  (Interpreter.notify_load, addr, size, value)
              | Stored (addr, size, value) ->
                  (Interpreter.notify_store, addr, size, value)
            in
            Machine.List.iter (bytes addr size value) ~f:(fun (addr, byte) ->
                let* addr = Value.of_word addr in
                let* byte = Value.of_word byte in
                notify addr byte))
      in
      let* () =
        Machine.List.iter written ~f:(fun (lo, hi) ->
            match Uc.mem_read e.uc lo Int64.(to_int_exn (hi - lo + 1L)) with
            | exception Uc.Error _ -> Machine.return ()
            | data ->
                String.to_list data
                |> List.mapi ~f:(fun i c -> (Int64.(lo + of_int i), c))
                |> Machine.List.iter ~f:(fun (a, c) ->
                    let* addr = Value.of_word (word e a) in
                    let* byte =
                      Value.of_word (Word.of_int ~width:8 (Char.to_int c))
                    in
                    Interpreter.notify_store addr byte))
      in
      push_owned e

  (* the registers, whose values Primus tracks, after the tracked
     values change, e.g., when taint is introduced, see [trace] *)
  let tracking e =
    let* version = Track.version in
    let* () =
      if version = e.seen then Machine.return ()
      else
        let* () = pull_regs e in
        let* version = Track.version in
        e.seen <- version;
        Hash_set.clear e.tracked;
        let* active = Track.active in
        let* shadowing =
          if active then Shadow.decide e else Machine.return e.shadowing
        in
        if not active then (
          Uc.taint_clear e.uc;
          e.shadowed <- false;
          Machine.return ())
        else if shadowing then Shadow.import e
        else
          (* the registers, rather than all the variables, e.g., the
             saved registers of the threads *)
          Machine.List.iter (Target.Regs.vars e.regs) ~f:(fun v ->
              match Target.Regs.owner e.regs (Var.name v) with
              | None -> Machine.return ()
              | Some r ->
                  let* set = Env.is_set v in
                  if not set then Machine.return ()
                  else
                    let* x = Env.get v in
                    let+ tracked = Track.is_tracked x in
                    if tracked then Hash_set.add e.tracked r)
    in
    sync_tracer e;
    Machine.return ()

  (* The bytes of the code around [addr], from Unicorn, if it has their
     page, as the program may have changed them there, otherwise from
     Primus, for [Lift.insn], which reads them from the instruction at
     [addr], or before it, see [trap]. *)
  let code_reader e addr =
    (* the bytes around the address, which may be any, e.g., of the
       program, that jumped near the end of the address space, without
       wrapping around it *)
    let max = Int64.of_int Primus.Lift.max_size in
    let below x = Stdlib.Int64.unsigned_compare x max < 0 in
    let before = if below addr then addr else max in
    let after =
      if Int64.(addr <> 0L) && below (Int64.neg addr) then Int64.neg addr
      else max
    in
    let lo = Int64.(addr - before) in
    let n = Int64.to_int_exn Int64.(before + after) in
    let in_uc x = Hashtbl.mem e.pages (page_of x) in
    let+ loaded =
      if in_uc lo && in_uc Int64.(lo + of_int n - 1L) then Machine.return [||]
      else Memory.load_bytes (word e lo) n
    in
    let byte x =
      if in_uc x then
        match Uc.mem_read e.uc x 1 with
        | b -> Some b.[0]
        | exception Uc.Error _ -> None
      else
        let i = Int64.(to_int_exn (x - lo)) in
        if i >= 0 && i < Array.length loaded then Option.map loaded.(i) ~f:fst
        else None
    in
    fun addr n ->
      let rec bytes i acc =
        if i = n then acc
        else
          match byte Int64.(addr + of_int i) with
          | Some c -> bytes (i + 1) (c :: acc)
          | None -> acc
      in
      String.of_char_list (List.rev (bytes 0 []))

  (* the failure at the instruction at [pc], that couldn't run, e.g.,
     that no lifter defined, which isn't lifted, see
     [Primus.Lift.undefined], or that is invalid *)
  let unrunnable e pc what =
    let addr = code_addr e pc in
    let* read = code_reader e addr in
    let* proj = Machine.get () in
    let code = read addr Primus.Lift.max_size in
    let* name =
      Machine.knowledge
        (Primus.Lift.undefined
           ?encoding:(arm_encoding e ~thumb:(in_thumb e pc))
           proj addr code)
    in
    match name with
    | Some name -> fail "the instruction %s at %Lx has no semantics" name pc
    | None -> fail "%s at %Lx" what pc

  (* the instruction at [addr], decoded from its current bytes, in
     the Thumb mode, if Unicorn runs the Thumb code *)
  let lift ?(thumb = false) e addr =
    let* read = code_reader e addr in
    Lift.insn ?encoding:(arm_encoding e ~thumb) ~read addr

  (* the accesses of the instruction at [addr], which are analyzed
     anew, if its bytes changed *)
  let analyze ?thumb e addr =
    let* insn = lift ?thumb e addr in
    let+ code = Lift.code addr in
    let code = Option.value code ~default:"" in
    match Hashtbl.find e.accesses addr with
    | Some access when String.equal access.code code -> access
    | _ ->
        let access =
          match insn with
          | Some (_, blks) -> access_of_blocks e.regs ~code blks
          | None -> { uses = []; defs = []; memory = false; code }
        in
        Hashtbl.set e.accesses ~key:addr ~data:access;
        access

  let word_of_insn e data =
    String.foldi data ~init:0L ~f:(fun i acc c ->
        let shift = if e.big_endian then 8 * (3 - i) else 8 * i in
        Int64.(acc lor (of_int (Char.to_int c) lsl shift)))

  (* Unicorn continues anew from [pc], outside of a delay slot of MIPS,
     whose branch, of the thread, that ran, or that Primus interpreted,
     is not pending, see build.cmake of libunicorn *)
  let fresh e pc =
    match e.arch with Mips -> Uc.reg_write e.uc e.pc pc | _ -> ()

  (* the branch of MIPS, whose delay slot is at [pc], or [pc], as
     Unicorn stops in the delay slot, e.g., at its fault, while the
     branch is pending, which runs again then, as its delay slot didn't
     run, and the address after a branch is its delay slot *)
  let branch_of_slot e pc =
    match e.arch with
    | Mips -> (
        let branch = Int64.(pc - 4L) in
        let+ () = ensure_page e branch in
        match uc_read e branch 4 with
        | data ->
            if mips_delayed ~r6:e.r6 (word_of_insn e data) then branch else pc
        | exception (Native.Missing _ | Native.Denied) -> pc)
    | _ -> Machine.return pc

  (* The system calls of Linux, that create and run the threads, see
     [threads], which run one at a time, in the engine, and switch, when
     the thread, that runs, waits, exits, or yields, or else, when its
     time slice ends, see [loop]. They switch only in the run, that
     created the first thread, as a stub, that runs a function of the
     program, returns to the thread, that called it. The calls of the
     processes, e.g., clone without CLONE_VM, and the other calls go to
     the intrinsic functions, as before. *)
  module Threads = struct
    type call =
      | Clone
      | Clone3
      | Futex
      | Set_tid_address
      | Gettid
      | Sched_yield
      | Exit
      | Exit_group
      | Set_tls  (** the register of TLS, e.g., of ARM, and MIPS *)
      | Set_thread_area  (** the descriptor of TLS of x86 *)

    (* how a system call fails: with the negated number of the error in
       its result, or with the number, and the flag of the error, e.g.,
       A3 of MIPS, or SO of CR0 of PowerPC *)
    type errors = Negated | Flagged of string

    (* the register of TLS, that clone sets: of Unicorn only, e.g.,
       FS_BASE of x86-64, see [extra_regs], of Primus, e.g., R2 of
       PowerPC, or the descriptor of the segment of x86, whose base is
       GS_BASE, see [Target.Segments] *)
    type tls = Extra of string | Reg of string | Descriptor

    (* the system calls of Linux: the registers of the number, of the
       arguments, after which the arguments are on the stack, from
       [stacked] of SP, of the result, the errors, the register of TLS,
       the numbers of the calls, and the order of the arguments of clone,
       which is (flags, stack, ptid, tls, ctid), if [backwards], as
       Linux calls it, and (flags, stack, ptid, ctid, tls) on x86-64 *)
    type abi = {
      number : string;
      args : string list;
      stacked : int;
      result : string;
      errors : errors;
      tls : tls;
      calls : (int * call) list;
      backwards : bool;
    }

    (* the numbers of the calls, from the tables of Linux *)
    let x86_64 =
      [
        (56, Clone);
        (435, Clone3);
        (202, Futex);
        (218, Set_tid_address);
        (186, Gettid);
        (24, Sched_yield);
        (60, Exit);
        (231, Exit_group);
      ]

    (* of AArch64 and RISC-V *)
    let generic =
      [
        (220, Clone);
        (435, Clone3);
        (98, Futex);
        (96, Set_tid_address);
        (178, Gettid);
        (124, Sched_yield);
        (93, Exit);
        (94, Exit_group);
      ]

    let i386 =
      [
        (120, Clone);
        (435, Clone3);
        (240, Futex);
        (258, Set_tid_address);
        (224, Gettid);
        (158, Sched_yield);
        (1, Exit);
        (252, Exit_group);
        (243, Set_thread_area);
      ]

    (* with set_tls, the private call of ARM *)
    let arm =
      [
        (120, Clone);
        (435, Clone3);
        (240, Futex);
        (256, Set_tid_address);
        (224, Gettid);
        (158, Sched_yield);
        (1, Exit);
        (248, Exit_group);
        (0xf0005, Set_tls);
      ]

    (* with set_thread_area, which sets the register of TLS *)
    let o32 =
      List.map
        ~f:(fun (n, call) -> (4000 + n, call))
        [
          (120, Clone);
          (435, Clone3);
          (238, Futex);
          (252, Set_tid_address);
          (222, Gettid);
          (162, Sched_yield);
          (1, Exit);
          (246, Exit_group);
          (283, Set_tls);
        ]

    let n64 =
      List.map
        ~f:(fun (n, call) -> (5000 + n, call))
        [
          (55, Clone);
          (435, Clone3);
          (194, Futex);
          (212, Set_tid_address);
          (178, Gettid);
          (23, Sched_yield);
          (58, Exit);
          (205, Exit_group);
          (242, Set_tls);
        ]

    let ppc =
      [
        (120, Clone);
        (435, Clone3);
        (221, Futex);
        (232, Set_tid_address);
        (207, Gettid);
        (158, Sched_yield);
        (1, Exit);
        (234, Exit_group);
      ]

    let abi (e : engine) =
      let regs prefix = List.map ~f:(sprintf "%s%d" prefix) in
      let linux ?(stacked = 0) ?(errors = Negated) ?(backwards = true) number
          args result tls calls =
        Some { number; args; stacked; result; errors; tls; calls; backwards }
      in
      match e.arch with
      | X86 when e.bytes = 8 ->
          linux ~backwards:false "RAX"
            [ "RDI"; "RSI"; "RDX"; "R10"; "R8"; "R9" ]
            "RAX" (Extra "FS_BASE") x86_64
      | X86 ->
          linux "EAX"
            [ "EBX"; "ECX"; "EDX"; "ESI"; "EDI"; "EBP" ]
            "EAX" Descriptor i386
      | Arm64 ->
          linux "R8"
            (regs "R" [ 0; 1; 2; 3; 4; 5 ])
            "R0" (Extra "TPIDR_EL0") generic
      | Arm ->
          linux "R7" (regs "R" [ 0; 1; 2; 3; 4; 5 ]) "R0" (Extra "C13_C0_3") arm
      | Mips when e.bytes = 4 ->
          (* the fifth and the sixth arguments are on the stack, after
             the space of the four in the registers *)
          linux ~stacked:16 ~errors:(Flagged "R7") "R2"
            (regs "R" [ 4; 5; 6; 7 ])
            "R2" (Extra "CP0_USERLOCAL") o32
      | Mips ->
          linux ~errors:(Flagged "R7") "R2"
            (regs "R" [ 4; 5; 6; 7; 8; 9 ])
            "R2" (Extra "CP0_USERLOCAL") n64
      | Ppc when e.bytes = 4 ->
          linux ~errors:(Flagged "CR0UN") "R0"
            (regs "R" [ 3; 4; 5; 6; 7; 8 ])
            "R3" (Reg "R2") ppc
      | Riscv when e.bytes = 8 ->
          linux "X17"
            (regs "X" [ 10; 11; 12; 13; 14; 15 ])
            "X10" (Reg "X4") generic
      | _ -> None

    let extra = extra_regs

    let call abi n =
      List.Assoc.find abi.calls ~equal:Int.equal (Int64.to_int_trunc n)

    let get e name =
      Option.value_map
        (Target.Regs.read_name e.regs name)
        ~default:0L ~f:int64_of_word

    let set e name x =
      ignore (Target.Regs.write_name e.regs name (word e x) : bool)

    (* the result of the call, which succeeded *)
    let succeed e abi x =
      set e abi.result x;
      match abi.errors with Flagged flag -> set e flag 0L | Negated -> ()

    let failure e abi errno =
      match abi.errors with
      | Negated -> set e abi.result (Int64.neg errno)
      | Flagged flag ->
          set e abi.result errno;
          set e flag 1L

    (* the instructions of the system calls, e.g., int 0x80 of x86 *)
    let is_trap { name; inputs; _ } =
      match name with
      | "intrinsic:syscall" | "intrinsic:svc" -> true
      | "intrinsic:interrupt" ->
          List.exists inputs ~f:(fun (v, x) ->
              String.equal (Var.name v) "intrinsic:x0"
              &&
              match x with
              | Bil.Int w ->
                  Word.equal w (Word.of_int ~width:(Word.bitwidth w) 0x80)
              | _ -> false)
      | _ -> false

    (* if the call of the intrinsic function [site] is of the threads,
       by its [number] *)
    let is_call e site number =
      is_trap site
      &&
      match abi e with
      | Some abi -> Option.is_some (call abi number)
      | None -> false

    (* the threads switch at the depth of the run, that created them *)
    let switchable e { depth; _ } =
      match depth with
      | None -> true
      | Some depth -> List.length e.frames = depth

    let bytes e x n =
      String.init n ~f:(fun i ->
          let i = if e.big_endian then n - 1 - i else i in
          Char.of_int_exn
            Int64.(to_int_exn (shift_right_logical x Int.(8 * i) land 0xFFL)))

    let value e data =
      let n = String.length data in
      List.init n ~f:Fn.id
      |> List.fold ~init:0L ~f:(fun acc i ->
          let i = if e.big_endian then i else n - 1 - i in
          Int64.((acc lsl 8) lor of_int (Char.to_int data.[i])))

    (* the parts of the [n] bytes from [addr], in their pages *)
    let chunks addr n =
      let rec chunks addr n acc =
        if n <= 0 then List.rev acc
        else
          let len =
            Int.min n (Int64.to_int_exn Int64.(page_of addr + page_size - addr))
          in
          chunks Int64.(addr + of_int len) (n - len) ((addr, len) :: acc)
      in
      chunks addr n []

    (* the bytes in Primus, if they all have the [access], as the page,
       whose locations are marked, e.g., tainted, is not in Unicorn, see
       [ensure_page] *)
    let primus_bytes e addr n access =
      let+ loaded = Memory.load_bytes (word e addr) n in
      if
        Array.for_all loaded ~f:(function
          | Some (_, p) -> access p
          | None -> false)
      then
        Some
          (String.of_array
             (Array.map loaded ~f:(fun b -> fst (Option.value_exn b))))
      else None

    let load_chunk e (addr, n) =
      let* () = ensure_page e addr in
      if Hashtbl.mem e.pages (page_of addr) then
        Machine.return
          (match uc_read e addr n with
          | data -> Some data
          | exception (Native.Missing _ | Native.Denied) -> None)
      else
        primus_bytes e addr n (fun (p : Primus.Memory.protection) -> p.readable)

    let store_chunk e addr data =
      let n = String.length data in
      let* () = ensure_page e addr in
      if Hashtbl.mem e.pages (page_of addr) then
        Machine.return
          (match uc_check_write e addr n with
          | () ->
              uc_write e addr data;
              true
          | exception (Native.Missing _ | Native.Denied) -> false)
      else
        primus_bytes e addr n (fun p -> p.writable) >>= function
        | None -> Machine.return false
        | Some _ -> Memory.store_bytes (word e addr) data >>| fun () -> true

    (* the bytes of the memory, or [None], if they are not accessible *)
    let load e addr n =
      Machine.List.map (chunks addr n) ~f:(load_chunk e)
      >>| Option.all
      >>| Option.map ~f:String.concat

    let store e addr data =
      chunks addr (String.length data)
      |> Machine.List.map ~f:(fun (a, n) ->
          store_chunk e a
            (String.sub data ~pos:(Int64.to_int_exn Int64.(a - addr)) ~len:n))
      >>| List.for_all ~f:Fn.id

    (* the futexes and the TIDs are the words of 32 bits *)
    let load32 e addr = load e addr 4 >>| Option.map ~f:(value e)
    let store32 e addr x = store e addr (bytes e x 4)

    (* the words of the size of the addresses *)
    let loadw e addr = load e addr e.bytes >>| Option.map ~f:(value e)
    let storew e addr x = store e addr (bytes e x e.bytes)

    (* the registers, that are set, the aliases too, e.g., EAX *)
    let registers e =
      Target.Regs.vars e.regs |> Machine.List.filter ~f:Env.is_set

    (* the value of the width of [x] *)
    let like x n =
      Value.of_word
        (Word.of_int64 ~width:(Word.bitwidth (Primus.Value.to_word x)) n)

    (* the registers of the thread [tid] are the values of the
       registers, that run, all of them, from Unicorn, if Primus doesn't
       have them, so that the thread doesn't get the registers of the
       other threads, and the aliases, that are set, with the [changed]
       ones, e.g., of the thread, that clone creates *)
    let copy e ?(changed = fun _ x -> Machine.return x) tid =
      let* () = pull e in
      let basis = Target.Regs.basis e.regs in
      let* () =
        Machine.List.iter basis ~f:(fun v ->
            let* x =
              Env.is_set v >>= function
              | true -> Env.get v
              | false -> (
                  match Target.Regs.read e.regs v with
                  | Some w -> Value.of_word w
                  | None -> Env.get v)
            in
            changed v x >>= Env.set (thread_var tid v))
      in
      registers e
      >>= Machine.List.iter ~f:(fun v ->
          if List.mem basis v ~equal:Var.equal then Machine.return ()
          else Env.get v >>= changed v >>= Env.set (thread_var tid v))

    (* the thread, that runs, which doesn't run anymore, and continues
       from [next] *)
    let park e ~next ~wait st =
      let+ () = copy e st.current in
      {
        tid = st.current;
        saved_extra = List.map (extra e) ~f:(fun id -> (id, read_extra e id));
        next;
        wait;
        clear = st.cleared;
        woken = false;
      }

    (* the bases of the segments of x86, that Primus has, e.g., FS_BASE,
       through which the programs of Windows read their TEB, which go to
       Unicorn, see [push_vars] *)
    let set_base e name x = Env.set (Var.create name (Type.imm (e.bytes * 8))) x

    (* the registers of the thread, that runs again, go to Primus and to
       Unicorn, and the ones, whose values are tracked, are tracked, see
       [trace] *)
    let resume e thread =
      let* () =
        Machine.List.iter (Target.Regs.basis e.regs) ~f:(fun v ->
            let saved = thread_var thread.tid v in
            Env.is_set saved >>= function
            | false -> Machine.return ()
            | true ->
                let* x = Env.get saved in
                let* () = Env.set v x in
                let w = Primus.Value.to_word x in
                if Target.Regs.write e.regs v w then
                  Hashtbl.set e.synced ~key:(Var.name v) ~data:w;
                let+ tracked = Track.is_tracked x in
                if tracked && not e.shadowing then
                  Hash_set.add e.tracked (Var.name v)
                else Hash_set.remove e.tracked (Var.name v))
      in
      (* the aliases, that are set, are of the thread, if their saved
         values are the bits of their registers, e.g., with their taint,
         and else are read anew, so that the ones of the other thread,
         e.g., tracked, don't stay *)
      let basis = Target.Regs.basis e.regs in
      let* () =
        registers e
        >>= Machine.List.iter ~f:(fun v ->
            if List.mem basis v ~equal:Var.equal then Machine.return ()
            else
              match Target.Regs.read e.regs v with
              | None -> Machine.return ()
              | Some w -> (
                  let saved = thread_var thread.tid v in
                  let* kept =
                    Env.is_set saved >>= function
                    | false -> Machine.return None
                    | true ->
                        let+ x = Env.get saved in
                        Option.some_if (Word.equal (Primus.Value.to_word x) w) x
                  in
                  match kept with
                  | Some x -> Env.set v x
                  | None -> Value.of_word w >>= Env.set v))
      in
      List.iter thread.saved_extra ~f:(fun (id, data) -> write_extra e id data);
      e.written <- [];
      (* the taint of the registers of the thread *)
      let* () = if e.shadowing then Shadow.import e else Machine.return () in
      (* the bases of the segments of x86 are of the thread in Primus
         too, if it has them *)
      Machine.List.iter thread.saved_extra ~f:(fun (id, data) ->
          match segment_base e id with
          | None -> Machine.return ()
          | Some name -> (
              let v = Var.create name (Type.imm (e.bytes * 8)) in
              let x = value { e with big_endian = false } data in
              Env.is_set v >>= function
              | false when Int64.(x = 0L) -> Machine.return ()
              | _ -> Value.of_word (word e x) >>= set_base e name))

    (* the next thread, that is ready, runs, after [parked], which was
       the thread, that ran, if it is not exited, or [None], if no thread
       is ready *)
    let switch e ?parked st =
      let others = st.others @ Option.to_list parked in
      match
        List.findi others ~f:(fun _ t ->
            match t.wait with Ready -> true | Waiting _ -> false)
      with
      | None -> Machine.return None
      | Some (i, next) ->
          let* () = resume e next in
          fresh e next.next;
          e.session.sliced_at <- clock ();
          let+ () =
            Machine.Local.put threads
              {
                st with
                current = next.tid;
                cleared = next.clear;
                woken = next.woken;
                others = List.filteri others ~f:(fun j _ -> j <> i);
              }
          in
          Some next.next

    (* the threads, that wait on [addr], at most [n], are ready, the
       first first *)
    let wake st addr n =
      let woken = ref 0 in
      let others =
        List.map st.others ~f:(fun t ->
            match t.wait with
            | Waiting addrs
              when List.mem addrs addr ~equal:Int64.equal && !woken < n ->
                incr woken;
                { t with wait = Ready; woken = true }
            | _ -> t)
      in
      ({ st with others }, !woken)

    let exit_process e code =
      let* code = Value.of_word (word e code) in
      let+ _ = Lisp.eval_fun "exit" [ code ] in
      None

    (* the time slice of a thread, while the other threads are ready,
       which is about the one of Linux *)
    let slice = 0.005

    let ready e st =
      switchable e st
      && List.exists st.others ~f:(fun t ->
          match t.wait with Ready -> true | Waiting _ -> false)

    (* the thread, that runs, is preempted at [pc], see [loop] *)
    let preempt e pc =
      let* st = Machine.Local.get threads in
      let* pc = branch_of_slot e (trampoline e pc) in
      let* parked = park e ~next:pc ~wait:Ready st in
      switch e ~parked st >>| function Some pc -> pc | None -> pc

    let flag flags bit = Int64.(flags land bit <> 0L)

    (* the thread, that runs, waits on [addrs], and continues from
       [next], when it is woken, or [timeout] continues it, if no thread
       is ready, e.g., with the error of the timeout *)
    let block e st ~next ~addrs ~timeout =
      if not (switchable e st) then
        fail "the thread %d waits in a run of a stub" st.current
      else
        let* parked = park e ~next ~wait:(Waiting addrs) st in
        switch e ~parked st >>= function
        | Some pc -> Machine.return (Some pc)
        | None -> (
            match timeout with
            | Some timeout -> timeout ()
            | None ->
                fail "the threads wait, the last one on %s"
                  (String.concat ~sep:", " (List.map addrs ~f:(sprintf "%Lx"))))

    (* the thread, that runs, exits with the [code], its TID is cleared,
       and the process exits, if it was the last one *)
    let exit_thread e st code =
      let* st =
        match st.cleared with
        | None -> Machine.return st
        | Some addr ->
            let+ _ = store32 e addr 0L in
            fst (wake st addr 1)
      in
      if List.is_empty st.others then exit_process e code
      else
        switch e st >>= function
        | Some pc -> Machine.return (Some pc)
        | None -> fail "the threads wait, after the thread %d exited" st.current

    (* the call of the thread, that runs, after which the thread, that
       runs then, continues from the address, or [None], if it isn't a
       call of the threads *)
    let syscall e ~next =
      match abi e with
      | None -> Machine.return None
      | Some abi -> (
          match call abi (get e abi.number) with
          | None -> Machine.return None
          | Some call -> (
              let* args =
                let regs = List.map abi.args ~f:(get e) in
                if abi.stacked = 0 then Machine.return regs
                else
                  let sp = get e (Var.name e.sp) in
                  let+ stacked =
                    Machine.List.map [ 0; 1 ] ~f:(fun i ->
                        loadw e
                          Int64.(sp + of_int Int.(abi.stacked + (i * e.bytes)))
                        >>| Option.value ~default:0L)
                  in
                  regs @ stacked
              in
              let arg i = List.nth_exn args i in
              let* st = Machine.Local.get threads in
              let return x =
                succeed e abi x;
                Machine.return (Some next)
              and error errno =
                failure e abi errno;
                Machine.return (Some next)
              in
              match call with
              | Clone3 -> error 38L
              | Gettid -> return (Int64.of_int st.current)
              | Set_tid_address ->
                  let* () =
                    Machine.Local.put threads { st with cleared = Some (arg 0) }
                  in
                  return (Int64.of_int st.current)
              | Exit_group -> exit_process e (arg 0)
              | Sched_yield ->
                  succeed e abi 0L;
                  if ready e st then
                    let* parked = park e ~next ~wait:Ready st in
                    switch e ~parked st
                  else Machine.return (Some next)
              | Set_tls -> (
                  match abi.tls with
                  | Extra name -> (
                      match Uc.reg e.arch name with
                      | Some id ->
                          Uc.reg_write e.uc id (arg 0);
                          return 0L
                      | None -> error 38L)
                  | Reg name ->
                      set e name (arg 0);
                      return 0L
                  | Descriptor -> error 38L)
              | Set_thread_area -> (
                  (* the descriptor of the segment of GS, whose entry the
                     program loads, which is the one of GS_BASE, see
                     [Target.Segments], if the program lets the kernel
                     choose it *)
                  let desc = arg 0 in
                  let* entry = load32 e desc in
                  let* base = load32 e Int64.(desc + 4L) in
                  match (entry, base) with
                  | Some entry, Some base ->
                      let* () =
                        if Int64.(entry = 0xFFFF_FFFFL) then
                          store32 e desc 2L >>| ignore
                        else Machine.return ()
                      in
                      ignore (Target.Segments.set e.uc "GS_BASE" base : bool);
                      let* () =
                        Value.of_word (word e base) >>= set_base e "GS_BASE"
                      in
                      return 0L
                  | _ -> error 14L)
              | Clone ->
                  let flags = arg 0 and stack = arg 1 and ptid = arg 2 in
                  let ctid, tls =
                    if abi.backwards then (arg 4, arg 3) else (arg 3, arg 4)
                  in
                  let settls = flag flags 0x80000L in
                  (* the processes, that don't share the memory *)
                  if not (flag flags 0x100L) then error 38L
                    (* EAGAIN, as RLIMIT_NPROC *)
                  else if too_many_threads st then error 11L
                  else
                    let tid = st.last + 1 in
                    let* () =
                      if flag flags 0x100000L then
                        store32 e ptid (Int64.of_int tid) >>| ignore
                      else Machine.return ()
                    in
                    let* () =
                      if flag flags 0x1000000L then
                        store32 e ctid (Int64.of_int tid) >>| ignore
                      else Machine.return ()
                    in
                    (* the base of the segment of x86 is in the
                       descriptor, see [Set_thread_area] *)
                    let* tls =
                      match abi.tls with
                      | Descriptor when settls ->
                          load32 e Int64.(tls + 4L) >>| Option.value ~default:0L
                      | _ -> Machine.return tls
                    in
                    (* the child has the values of the registers of
                       the parent, e.g., their taint, but the result,
                       the stack, and TLS *)
                    let* () =
                      copy e tid ~changed:(fun v x ->
                          let name = Var.name v in
                          if
                            String.equal name abi.result
                            ||
                            match abi.errors with
                            | Flagged flag -> String.equal name flag
                            | Negated -> false
                          then like x 0L
                          else if Var.equal v e.sp && Int64.(stack <> 0L) then
                            like x stack
                          else if
                            settls
                            &&
                            match abi.tls with
                            | Reg reg -> String.equal name reg
                            | Extra _ | Descriptor -> false
                          then like x tls
                          else Machine.return x)
                    in
                    let tls_id =
                      if not settls then None
                      else
                        match abi.tls with
                        | Extra name -> Uc.reg e.arch name
                        | Descriptor -> Uc.reg e.arch "GS_BASE"
                        | Reg _ -> None
                    in
                    let child =
                      {
                        tid;
                        saved_extra =
                          List.map (extra e) ~f:(fun id ->
                              let data = read_extra e id in
                              if Option.equal Int.equal (Some id) tls_id then
                                ( id,
                                  bytes
                                    { e with big_endian = false }
                                    tls (String.length data) )
                              else (id, data));
                        next;
                        wait = Ready;
                        clear =
                          (if flag flags 0x200000L then Some ctid else None);
                        woken = false;
                      }
                    in
                    let* () =
                      Machine.Local.put threads
                        {
                          st with
                          others = st.others @ [ child ];
                          last = tid;
                          depth =
                            Some
                              (Option.value st.depth
                                 ~default:(List.length e.frames));
                        }
                    in
                    return (Int64.of_int tid)
              | Futex -> (
                  let addr = arg 0
                  and value = Int64.(arg 2 land 0xFFFF_FFFFL) in
                  match Int64.to_int_trunc (arg 1) land 0x7F with
                  | 0 | 9 -> (
                      load32 e addr >>= function
                      | None -> error 14L
                      | Some x when Int64.(x <> value) -> error 11L
                      | Some _ ->
                          (* it returns 0, when it is woken *)
                          succeed e abi 0L;
                          block e st ~next ~addrs:[ addr ]
                            ~timeout:
                              (Option.some_if
                                 Int64.(arg 3 <> 0L)
                                 (fun () -> error 110L)))
                  | 1 | 10 ->
                      let st, woken = wake st addr (Int64.to_int_trunc value) in
                      let* () = Machine.Local.put threads st in
                      return (Int64.of_int woken)
                  | _ -> error 38L)
              | Exit -> exit_thread e st (arg 0)))

    (* The threads of the programs of Windows, that the functions of
       KERNEL32, e.g., CreateThread, and of msvcrt, e.g., _beginthreadex,
       create, and their objects, e.g., the events, the mutexes, the
       semaphores, the critical sections, the SRW locks, the condition
       variables, the addresses of WaitOnAddress, and the slots of TLS,
       which the executor runs, instead of their stubs, when the program
       calls them, on x86 and x86-64.

       The objects, whose handles are their addresses, are in the memory,
       that malloc allocates, as the stacks and the TEBs of the threads,
       so that the checkpoints keep them. The thread, that waits, calls
       the function again, when it is woken, as it continues from its
       entry, see [block], and the condition variables reacquire their
       locks then, see [woken]. A thread, whose function returns, returns
       to [exit_addr], which is not mapped, and exits with its result.
       The timeouts expire only when no thread is ready, as the time
       doesn't pass. *)
    module Windows = struct
      let wide e = e.bytes = 8
      let result e = if wide e then "RAX" else "EAX"

      (* the return address of the threads, that aren't main *)
      let exit_addr = 0xFFFF_F000L
      let infinite = 0xFFFF_FFFFL
      let timeout = 0x102L
      let failed = 0xFFFF_FFFFL

      (* the register of the base of TEB, and the offsets of its fields:
         NtTib.Self, NtTib.StackBase, NtTib.StackLimit, ClientId, the
         PEB, TlsSlots, and Win32ThreadInfo, which has the object of the
         thread here, and the offset of TlsBitmapBits of PEB *)
      type teb = {
        base : string;
        self : int;
        stack_base : int;
        stack_limit : int;
        client : int;
        peb : int;
        slots : int;
        info : int;
        bitmap : int;
      }

      let teb e =
        if wide e then
          {
            base = "GS_BASE";
            self = 0x30;
            stack_base = 0x8;
            stack_limit = 0x10;
            client = 0x40;
            peb = 0x60;
            slots = 0x1480;
            info = 0x78;
            bitmap = 0x80;
          }
        else
          {
            base = "FS_BASE";
            self = 0x18;
            stack_base = 0x4;
            stack_limit = 0x8;
            client = 0x20;
            peb = 0x30;
            slots = 0xE10;
            info = 0x40;
            bitmap = 0x44;
          }

      (* the TEB of the thread, that runs *)
      (* the base of the segment of the TEB, which is in its descriptor in
         the protected mode, rather than in the register, e.g., of the
         lifted engine, see [read_extra] *)
      let current_teb e =
        match Uc.reg X86 (teb e).base with
        | Some id ->
            String.foldi (read_extra e id) ~init:0L ~f:(fun i acc c ->
                Int64.(acc lor (of_int (Char.to_int c) lsl Int.(8 * i))))
        | None -> 0L

      (* the arguments of the functions of Windows, in RCX, RDX, R8, R9,
         and on the stack, after the return address and the shadow
         space, on x86-64, and on the stack on x86 *)
      let arg e i =
        let sp = get e (Var.name e.sp) in
        if wide e && i < 4 then
          Machine.return (get e (List.nth_exn [ "RCX"; "RDX"; "R8"; "R9" ] i))
        else
          let off = if wide e then 0x28 + (8 * (i - 4)) else 4 + (4 * i) in
          loadw e Int64.(sp + of_int off) >>| Option.value ~default:0L

      (* the function returns [x], after which the thread continues from
         the return address, and pops its [n] arguments on x86, as
         stdcall does, unless it is cdecl, e.g., of msvcrt *)
      let finish e ?(cdecl = false) n x =
        let sp = get e (Var.name e.sp) in
        loadw e sp >>= function
        | None -> fail "the return address of %Lx is not accessible" sp
        | Some ret ->
            set e (result e) x;
            let pops = if wide e || cdecl then 0 else 4 * n in
            set e (Var.name e.sp) Int64.(sp + of_int Int.(e.bytes + pops));
            Machine.return ret

      (* the objects, whose handles are their addresses, which start with
         [magic], and their kind, and whose fields are the words of 32
         bits *)
      let magic = 0x57504142L

      type kind = Thread | Event | Mutex | Semaphore

      let kinds = [ (1L, Thread); (2L, Event); (3L, Mutex); (4L, Semaphore) ]

      let code kind =
        fst (List.find_exn kinds ~f:(fun (_, k) -> Poly.equal k kind))

      let field h i = Int64.(h + of_int Int.(4 * i))
      let read e h i = load32 e (field h i) >>| Option.value ~default:0L
      let write e h i x = store32 e (field h i) x >>| ignore

      (* the fields of the objects, after the magic and the kind *)
      let tid = 2 (* of the thread *)
      let exited = 3
      let exit_code = 4
      let suspended = 5
      let manual = 2 (* of the event *)
      let signaled = 3
      let owner = 2 (* of the mutex *)
      let count = 3
      let available = 2 (* of the semaphore *)
      let maximum = 3

      (* the thread, that is suspended, waits on the field of the count,
         until it is resumed *)
      let resumed h = field h suspended

      let kind e h =
        if Int64.(h = 0L || h land 3L <> 0L) then Machine.return None
        else
          load32 e h >>= function
          | Some m when Int64.(m = magic) ->
              read e h 1 >>| List.Assoc.find kinds ~equal:Int64.equal
          | _ -> Machine.return None

      (* the memory of [n] bytes, aligned to 16 bytes, as malloc
         aligns the chunks to the program break *)
      let allocate e n =
        let* size = Value.of_word (word e (Int64.of_int (n + 15))) in
        let* p = Lisp.eval_fun "malloc" [ size ] in
        let p = int64_of_word (Primus.Value.to_word p) in
        if Int64.(p = 0L) then fail "malloc can't allocate %d bytes" n
        else Machine.return Int64.((p + 15L) land lnot 15L)

      let create_object e kind fields =
        let* h = allocate e 32 in
        let* () =
          Machine.List.iter
            (List.mapi ([ magic; code kind ] @ fields) ~f:(fun i x -> (i, x)))
            ~f:(fun (i, x) -> write e h i x)
        in
        Machine.return h

      (* the object [h] of the [kind] is signaled, and the thread [me]
         acquires it, if it is, e.g., the mutex, or the semaphore *)
      let is_signaled e ~me h kind =
        match kind with
        | Thread -> read e h exited >>| Int64.equal 1L
        | Event -> read e h signaled >>| Int64.equal 1L
        | Mutex -> read e h owner >>| fun o -> Int64.(o = 0L || o = me)
        | Semaphore -> read e h available >>| fun n -> Int64.(n > 0L)

      let acquire e ~me h kind =
        match kind with
        | Thread -> Machine.return ()
        | Event ->
            read e h manual >>= fun manual ->
            if Int64.(manual = 0L) then write e h signaled 0L
            else Machine.return ()
        | Mutex ->
            let* () = write e h owner me in
            read e h count >>= fun n -> write e h count Int64.(n + 1L)
        | Semaphore ->
            read e h available >>= fun n -> write e h available Int64.(n - 1L)

      let wake_all e st addr =
        let st, _ = wake st addr Int.max_value in
        let+ () = Machine.Local.put threads st in
        st

      (* the slots of TLS, which the bits of TlsBitmapBits of PEB
         allocate *)
      let bitmap e =
        let t = teb e in
        let* peb = loadw e Int64.(current_teb e + of_int t.peb) in
        let peb = Option.value peb ~default:0L in
        let addr = Int64.(peb + of_int t.bitmap) in
        let+ bits = load e addr 8 in
        (addr, Option.value_map bits ~default:0L ~f:(value e))

      let slot e i =
        let t = teb e in
        Int64.(current_teb e + of_int t.slots + (i * of_int e.bytes))

      (* the critical section: LockCount, RecursionCount, and
         OwningThread, which is the TID here *)
      let section e cs =
        if wide e then (Int64.(cs + 8L), Int64.(cs + 12L), Int64.(cs + 16L))
        else (Int64.(cs + 4L), Int64.(cs + 8L), Int64.(cs + 12L))

      let enter_section e ~me cs =
        let lock, recursion, owner = section e cs in
        let* o = loadw e owner >>| Option.value ~default:0L in
        if Int64.(o = 0L) then
          let* _ = storew e owner me in
          let* _ = store32 e recursion 1L in
          let+ _ = store32 e lock 0L in
          true
        else if Int64.(o = me) then
          let* r = load32 e recursion >>| Option.value ~default:0L in
          let* _ = store32 e recursion Int64.(r + 1L) in
          let* l = load32 e lock >>| Option.value ~default:0L in
          let+ _ = store32 e lock Int64.((l + 1L) land 0xFFFF_FFFFL) in
          true
        else Machine.return false

      (* the thread [me] leaves the section, [all] the times, e.g., as it
         waits on a condition variable, and returns if it owned it *)
      let leave_section e st ~me ?(all = false) cs =
        let lock, recursion, owner = section e cs in
        let* o = loadw e owner >>| Option.value ~default:0L in
        if Int64.(o <> me) then Machine.return (st, false)
        else
          let* r = load32 e recursion >>| Option.value ~default:1L in
          if Int64.(r > 1L) && not all then
            let* _ = store32 e recursion Int64.(r - 1L) in
            Machine.return (st, true)
          else
            let* _ = storew e owner 0L in
            let* _ = store32 e recursion 0L in
            let* _ = store32 e lock 0xFFFF_FFFFL in
            let st, _ = wake st cs 1 in
            let+ () = Machine.Local.put threads st in
            (st, true)

      (* the SRW lock is 1, if it is exclusive, and twice the number of
         its shared owners otherwise *)
      let acquire_srw e ~shared lock =
        let* w = loadw e lock >>| Option.value ~default:0L in
        if shared && Int64.(w land 1L = 0L) then storew e lock Int64.(w + 2L)
        else if (not shared) && Int64.(w = 0L) then storew e lock 1L
        else Machine.return false

      let release_srw e st lock =
        let* w = loadw e lock >>| Option.value ~default:0L in
        let w = if Int64.(w = 1L) then 0L else Int64.(max 0L (w - 2L)) in
        let* _ = storew e lock w in
        if Int64.(w = 0L) then wake_all e st lock else Machine.return st

      (* the thread [tid], whose function starts at [start] with the
         [param], on the stack of the [size], which is suspended, if
         [suspended], and whose object is the result *)
      let create e st ~start ~param ~size ~suspended =
        let tid = st.last + 1 in
        let t = teb e in
        (* the size of the program, which may be any, is at most 256 MB *)
        let size =
          if Int64.(size <= 0L) then 0x40000
          else
            Int64.(
              to_int_exn
                ((min (max size 0x10000L) 0x1000_0000L + 0xFFFFL)
                land lnot 0xFFFFL))
        in
        let* stack = allocate e size in
        let* teb = allocate e 0x2000 in
        let* h =
          create_object e Thread
            [ Int64.of_int tid; 0L; 259L; (if suspended then 1L else 0L) ]
        in
        let* peb =
          loadw e Int64.(current_teb e + of_int t.peb)
          >>| Option.value ~default:0L
        in
        let top = Int64.((stack + of_int size) land lnot 15L) in
        let* _ = store e teb (String.make 0x2000 '\000') in
        let field off x = storew e Int64.(teb + of_int off) x >>| ignore in
        let* () = field t.self teb in
        let* () = field t.stack_base top in
        let* () = field t.stack_limit stack in
        let* () = field t.peb peb in
        let* () = field t.client 1L in
        let* () = field (t.client + e.bytes) (Int64.of_int tid) in
        let* () = field t.info h in
        (* the end of the chain of the handlers of SEH of x86 *)
        let* () = if wide e then Machine.return () else field 0 0xFFFF_FFFFL in
        (* the function returns to [exit_addr], with the stack aligned,
           as at the entries of the functions *)
        let sp = if wide e then Int64.(top - 0x38L) else Int64.(top - 0x14L) in
        let* _ = storew e sp exit_addr in
        let* () =
          if wide e then Machine.return ()
          else storew e Int64.(sp + 4L) param >>| ignore
        in
        let* () =
          copy e tid ~changed:(fun v x ->
              let name = Var.name v in
              if Var.equal v e.sp then like x sp
              else if wide e && String.equal name "RCX" then like x param
              else if String.equal name t.base then like x teb
              else Machine.return x)
        in
        let base = Uc.reg X86 t.base in
        let child =
          {
            tid;
            saved_extra =
              List.map (extra e) ~f:(fun id ->
                  let data = read_extra e id in
                  if Option.equal Int.equal (Some id) base then
                    (id, bytes e teb (String.length data))
                  else (id, data));
            next = start;
            wait = (if suspended then Waiting [ resumed h ] else Ready);
            clear = None;
            woken = false;
          }
        in
        let+ () =
          Machine.Local.put threads
            {
              st with
              others = st.others @ [ child ];
              last = tid;
              depth =
                Some (Option.value st.depth ~default:(List.length e.frames));
            }
        in
        h

      (* the thread, that runs, exits with the [code], whose object is
         signaled, and the process exits, if it was the last one *)
      let exit_thread e st code =
        let t = teb e in
        let* h =
          loadw e Int64.(current_teb e + of_int t.info)
          >>| Option.value ~default:0L
        in
        let* st =
          kind e h >>= function
          | Some Thread ->
              let* () = write e h exited 1L in
              let* () = write e h exit_code Int64.(code land 0xFFFF_FFFFL) in
              wake_all e st h
          | _ -> Machine.return st
        in
        if List.is_empty st.others then exit_process e code
        else
          switch e st >>= function
          | Some pc -> Machine.return (Some pc)
          | None ->
              fail "the threads wait, after the thread %d exited" st.current

      (* the functions, by their names, and the numbers of their
         arguments *)
      let functions =
        [
          ("CreateThread", 6);
          ("_beginthreadex", 6);
          ("_beginthread", 3);
          ("ExitThread", 1);
          ("_endthreadex", 1);
          ("_endthread", 0);
          ("GetCurrentThreadId", 0);
          ("GetCurrentThread", 0);
          ("GetThreadId", 1);
          ("GetExitCodeThread", 2);
          ("ResumeThread", 1);
          ("CloseHandle", 1);
          ("Sleep", 1);
          ("SleepEx", 2);
          ("SwitchToThread", 0);
          ("WaitForSingleObject", 2);
          ("WaitForSingleObjectEx", 3);
          ("WaitForMultipleObjects", 4);
          ("WaitForMultipleObjectsEx", 5);
          ("CreateEventA", 4);
          ("CreateEventW", 4);
          ("CreateEventExA", 4);
          ("CreateEventExW", 4);
          ("SetEvent", 1);
          ("ResetEvent", 1);
          ("CreateMutexA", 3);
          ("CreateMutexW", 3);
          ("ReleaseMutex", 1);
          ("CreateSemaphoreA", 4);
          ("CreateSemaphoreW", 4);
          ("ReleaseSemaphore", 3);
          ("InitializeCriticalSection", 1);
          ("InitializeCriticalSectionAndSpinCount", 2);
          ("InitializeCriticalSectionEx", 3);
          ("DeleteCriticalSection", 1);
          ("EnterCriticalSection", 1);
          ("TryEnterCriticalSection", 1);
          ("LeaveCriticalSection", 1);
          ("InitializeSRWLock", 1);
          ("AcquireSRWLockExclusive", 1);
          ("AcquireSRWLockShared", 1);
          ("TryAcquireSRWLockExclusive", 1);
          ("TryAcquireSRWLockShared", 1);
          ("ReleaseSRWLockExclusive", 1);
          ("ReleaseSRWLockShared", 1);
          ("InitializeConditionVariable", 1);
          ("SleepConditionVariableCS", 3);
          ("SleepConditionVariableSRW", 4);
          ("WakeConditionVariable", 1);
          ("WakeAllConditionVariable", 1);
          ("WaitOnAddress", 4);
          ("WakeByAddressSingle", 1);
          ("WakeByAddressAll", 1);
          ("TlsAlloc", 0);
          ("TlsFree", 1);
          ("TlsGetValue", 1);
          ("TlsSetValue", 2);
          ("FlsAlloc", 1);
          ("FlsFree", 1);
          ("FlsGetValue", 1);
          ("FlsSetValue", 2);
        ]

      let is_pe =
        Machine.gets Project.specification >>| fun spec ->
        match Ogre.eval (Ogre.request Image.Scheme.format) spec with
        | Ok (Some "coff") -> true
        | _ -> false

      (* the function of Windows at [entry], which the thread, that runs,
         calls, after which the thread, that runs then, continues from
         the address, or [None], if it isn't a function of the threads *)
      let call e entry =
        match
          Option.bind (function_name e entry) ~f:(fun name ->
              Option.map (List.Assoc.find functions ~equal:String.equal name)
                ~f:(fun n -> (name, n)))
        with
        | None -> Machine.return None
        | Some _ when not (Poly.equal e.arch Uc.X86) -> Machine.return None
        | Some (name, n) -> (
            is_pe >>= function
            | false -> Machine.return None
            | true -> (
                let* () = pull e in
                let* args =
                  Machine.List.map (List.init n ~f:Fn.id) ~f:(arg e)
                in
                let arg i = List.nth_exn args i in
                (* the thread was woken, e.g., from the condition
                   variable, which is the call again *)
                let* st = Machine.Local.get threads in
                let woken = st.woken in
                let st = { st with woken = false } in
                let* () = Machine.Local.put threads st in
                let me = Int64.of_int st.current in
                let cdecl = String.is_prefix name ~prefix:"_" in
                let return x = finish e ~cdecl n x >>| Option.some in
                let bool b = return (if b then 1L else 0L) in
                (* waits on the [addrs], after which the function is
                   called again, or returns [timeout], if it waits for
                   the [ms], and no thread is ready *)
                let wait ?(ms = infinite) ?(result = timeout) addrs =
                  if Int64.(ms land 0xFFFF_FFFFL = 0L) then return result
                  else
                    block e st ~next:entry ~addrs
                      ~timeout:
                        (Option.some_if
                           Int64.(ms land 0xFFFF_FFFFL <> infinite)
                           (fun () -> return result))
                in
                let yield x =
                  let* ret = finish e ~cdecl n x in
                  if ready e st then
                    let* parked = park e ~next:ret ~wait:Ready st in
                    switch e ~parked st
                  else Machine.return (Some ret)
                in
                let create ~start ~param ~size ~flags ~ptid =
                  (* NULL, as the threads, that the program may create,
                     are limited *)
                  if too_many_threads st then return 0L
                  else
                    let* h =
                      create e st ~start ~param ~size ~suspended:(flag flags 4L)
                    in
                    let* () =
                      if Int64.(ptid <> 0L) then
                        store32 e ptid (Int64.of_int (st.last + 1)) >>| ignore
                      else Machine.return ()
                    in
                    return h
                in
                let objects handles =
                  Machine.List.map handles ~f:(fun h ->
                      kind e h >>| Option.map ~f:(fun k -> (h, k)))
                  >>| Option.all
                in
                match name with
                | "CreateThread" | "_beginthreadex" ->
                    create ~start:(arg 2) ~param:(arg 3) ~size:(arg 1)
                      ~flags:(arg 4) ~ptid:(arg 5)
                | "_beginthread" ->
                    create ~start:(arg 0) ~param:(arg 2) ~size:(arg 1) ~flags:0L
                      ~ptid:0L
                | "ExitThread" | "_endthreadex" -> exit_thread e st (arg 0)
                | "_endthread" -> exit_thread e st 0L
                | "GetCurrentThreadId" -> return me
                | "GetCurrentThread" -> return (-2L)
                | "GetThreadId" -> (
                    kind e (arg 0) >>= function
                    | Some Thread -> read e (arg 0) tid >>= return
                    | _ -> return 0L)
                | "GetExitCodeThread" -> (
                    kind e (arg 0) >>= function
                    | Some Thread ->
                        let* code = read e (arg 0) exit_code in
                        let* _ = store32 e (arg 1) code in
                        return 1L
                    | _ -> return 0L)
                | "ResumeThread" -> (
                    let h = arg 0 in
                    kind e h >>= function
                    | Some Thread ->
                        let* n = read e h suspended in
                        let* st =
                          if Int64.(n = 1L) then
                            let* () = write e h suspended 0L in
                            wake_all e st (resumed h)
                          else if Int64.(n > 1L) then
                            write e h suspended Int64.(n - 1L) >>| fun () -> st
                          else Machine.return st
                        in
                        ignore st;
                        return n
                    | _ -> return failed)
                | "CloseHandle" -> return 1L
                | "Sleep" | "SleepEx" -> yield 0L
                | "SwitchToThread" -> yield (if ready e st then 1L else 0L)
                | "WaitForSingleObject" | "WaitForSingleObjectEx" -> (
                    let h = arg 0 in
                    kind e h >>= function
                    | None -> return failed
                    | Some kind -> (
                        is_signaled e ~me h kind >>= function
                        | true -> acquire e ~me h kind >>= fun () -> return 0L
                        | false -> wait ~ms:(arg 1) [ h ]))
                | "WaitForMultipleObjects" | "WaitForMultipleObjectsEx" -> (
                    (* at most MAXIMUM_WAIT_OBJECTS handles, a DWORD *)
                    let count =
                      Int64.(to_int_trunc (arg 0 land 0xFFFF_FFFFL))
                    in
                    if count < 1 || count > 64 then return failed
                    else
                      let* handles =
                        Machine.List.map (List.init count ~f:Fn.id) ~f:(fun i ->
                            loadw e Int64.(arg 1 + of_int Int.(i * e.bytes))
                            >>| Option.value ~default:0L)
                      in
                      objects handles >>= function
                      | None -> return failed
                      | Some objects -> (
                          let ms = arg 3 in
                          if Int64.(arg 2 <> 0L) then
                            let* all =
                              Machine.List.for_all objects ~f:(fun (h, k) ->
                                  is_signaled e ~me h k)
                            in
                            if all then
                              let* () =
                                Machine.List.iter objects ~f:(fun (h, k) ->
                                    acquire e ~me h k)
                              in
                              return 0L
                            else wait ~ms handles
                          else
                            let* first =
                              Machine.List.find_map
                                (List.mapi objects ~f:(fun i o -> (i, o)))
                                ~f:(fun (i, (h, k)) ->
                                  is_signaled e ~me h k >>| fun s ->
                                  Option.some_if s (i, h, k))
                            in
                            match first with
                            | Some (i, h, k) ->
                                acquire e ~me h k >>= fun () ->
                                return (Int64.of_int i)
                            | None -> wait ~ms handles))
                | "CreateEventA" | "CreateEventW" ->
                    create_object e Event
                      [
                        (if Int64.(arg 1 <> 0L) then 1L else 0L);
                        (if Int64.(arg 2 <> 0L) then 1L else 0L);
                      ]
                    >>= return
                | "CreateEventExA" | "CreateEventExW" ->
                    create_object e Event
                      [
                        (if flag (arg 2) 1L then 1L else 0L);
                        (if flag (arg 2) 2L then 1L else 0L);
                      ]
                    >>= return
                | "SetEvent" | "ResetEvent" -> (
                    let h = arg 0 in
                    kind e h >>= function
                    | Some Event ->
                        let set = String.equal name "SetEvent" in
                        let* () = write e h signaled (if set then 1L else 0L) in
                        let* _ =
                          if set then wake_all e st h else Machine.return st
                        in
                        return 1L
                    | _ -> return 0L)
                | "CreateMutexA" | "CreateMutexW" ->
                    (if Int64.(arg 1 <> 0L) then [ me; 1L ] else [ 0L; 0L ])
                    |> create_object e Mutex >>= return
                | "ReleaseMutex" -> (
                    let h = arg 0 in
                    kind e h >>= function
                    | Some Mutex -> (
                        read e h owner >>= function
                        | o when Int64.(o = me) ->
                            let* n = read e h count in
                            let* () = write e h count Int64.(n - 1L) in
                            let* _ =
                              if Int64.(n <= 1L) then
                                write e h owner 0L >>= fun () -> wake_all e st h
                              else Machine.return st
                            in
                            return 1L
                        | _ -> return 0L)
                    | _ -> return 0L)
                | "CreateSemaphoreA" | "CreateSemaphoreW" ->
                    create_object e Semaphore [ arg 1; arg 2 ] >>= return
                | "ReleaseSemaphore" -> (
                    let h = arg 0 in
                    kind e h >>= function
                    | Some Semaphore ->
                        let* n = read e h available in
                        let* limit = read e h maximum in
                        if Int64.(n + arg 1 > limit) then return 0L
                        else
                          let* () = write e h available Int64.(n + arg 1) in
                          let* () =
                            if Int64.(arg 2 <> 0L) then
                              store32 e (arg 2) n >>| ignore
                            else Machine.return ()
                          in
                          let* _ = wake_all e st h in
                          return 1L
                    | _ -> return 0L)
                | "InitializeCriticalSection"
                | "InitializeCriticalSectionAndSpinCount"
                | "InitializeCriticalSectionEx" ->
                    let lock, recursion, owner = section e (arg 0) in
                    let* _ = storew e (arg 0) 0L in
                    let* _ = store32 e lock 0xFFFF_FFFFL in
                    let* _ = store32 e recursion 0L in
                    let* _ = storew e owner 0L in
                    return 1L
                | "DeleteCriticalSection" -> return 0L
                | "EnterCriticalSection" -> (
                    enter_section e ~me (arg 0) >>= function
                    | true -> return 0L
                    | false -> wait [ arg 0 ])
                | "TryEnterCriticalSection" ->
                    enter_section e ~me (arg 0) >>= bool
                | "LeaveCriticalSection" ->
                    leave_section e st ~me (arg 0) >>= fun _ -> return 0L
                | "InitializeSRWLock" | "InitializeConditionVariable" ->
                    storew e (arg 0) 0L >>= fun _ -> return 0L
                | "AcquireSRWLockExclusive" | "AcquireSRWLockShared" -> (
                    let shared = String.equal name "AcquireSRWLockShared" in
                    acquire_srw e ~shared (arg 0) >>= function
                    | true -> return 0L
                    | false -> wait [ arg 0 ])
                | "TryAcquireSRWLockExclusive" | "TryAcquireSRWLockShared" ->
                    let shared = String.equal name "TryAcquireSRWLockShared" in
                    acquire_srw e ~shared (arg 0) >>= bool
                | "ReleaseSRWLockExclusive" | "ReleaseSRWLockShared" ->
                    release_srw e st (arg 0) >>= fun _ -> return 0L
                | "SleepConditionVariableCS" | "SleepConditionVariableSRW" ->
                    let cv = arg 0 and lock = arg 1 and ms = arg 2 in
                    let cs = String.equal name "SleepConditionVariableCS" in
                    let shared = (not cs) && flag (arg 3) 1L in
                    let reacquire () =
                      if cs then enter_section e ~me lock
                      else acquire_srw e ~shared lock
                    in
                    if woken then
                      (* woken, the thread reacquires the lock, or waits
                         for it, after which it is woken again *)
                      reacquire () >>= function
                      | true -> return 1L
                      | false -> (
                          let* parked =
                            park e ~next:entry ~wait:(Waiting [ lock ]) st
                          in
                          switch e ~parked:{ parked with woken = true } st
                          >>= function
                          | Some pc -> Machine.return (Some pc)
                          | None ->
                              fail "the threads wait, the last one on %Lx" lock)
                    else
                      let* st =
                        if cs then leave_section e st ~me ~all:true lock >>| fst
                        else release_srw e st lock
                      in
                      if Int64.(ms land 0xFFFF_FFFFL = 0L) then
                        reacquire () >>= fun _ -> return 0L
                      else
                        block e st ~next:entry ~addrs:[ cv ]
                          ~timeout:
                            (Option.some_if
                               Int64.(ms land 0xFFFF_FFFFL <> infinite)
                               (fun () -> reacquire () >>= fun _ -> return 0L))
                | "WakeConditionVariable" ->
                    let st, _ = wake st (arg 0) 1 in
                    let* () = Machine.Local.put threads st in
                    return 0L
                | "WakeAllConditionVariable" ->
                    wake_all e st (arg 0) >>= fun _ -> return 0L
                | "WaitOnAddress" -> (
                    match arg 2 with
                    (* the sizes of the addresses, that it compares *)
                    | (1L | 2L | 4L | 8L) as size -> (
                        let addr = arg 0 and size = Int64.to_int_exn size in
                        let* x = load e addr size in
                        let* y = load e (arg 1) size in
                        match (x, y) with
                        | Some x, Some y when String.equal x y ->
                            if Int64.(arg 3 land 0xFFFF_FFFFL = 0L) then
                              return 0L
                            else
                              (* it returns TRUE, when it is woken *)
                              let* ret = finish e n 1L in
                              block e st ~next:ret ~addrs:[ addr ]
                                ~timeout:
                                  (Option.some_if
                                     Int64.(arg 3 land 0xFFFF_FFFFL <> infinite)
                                     (fun () ->
                                       set e (result e) 0L;
                                       Machine.return (Some ret)))
                        | _ -> return 1L)
                    | _ -> return 0L)
                | "WakeByAddressSingle" ->
                    let st, _ = wake st (arg 0) 1 in
                    let* () = Machine.Local.put threads st in
                    return 0L
                | "WakeByAddressAll" ->
                    wake_all e st (arg 0) >>= fun _ -> return 0L
                | "TlsAlloc" | "FlsAlloc" -> (
                    let* addr, bits = bitmap e in
                    match
                      List.find (List.init 64 ~f:Fn.id) ~f:(fun i ->
                          Int64.(bits land (1L lsl i) = 0L))
                    with
                    | None -> return failed
                    | Some i ->
                        let* _ =
                          store e addr (bytes e Int64.(bits lor (1L lsl i)) 8)
                        in
                        let* _ = storew e (slot e (Int64.of_int i)) 0L in
                        return (Int64.of_int i))
                | "TlsFree" | "FlsFree" ->
                    let* addr, bits = bitmap e in
                    let i = Int64.(arg 0 land 63L) in
                    let* _ =
                      store e addr
                        (bytes e Int64.(bits land lnot (1L lsl to_int_exn i)) 8)
                    in
                    return 1L
                | "TlsGetValue" | "FlsGetValue" ->
                    loadw e (slot e (arg 0))
                    >>| Option.value ~default:0L >>= return
                | "TlsSetValue" | "FlsSetValue" ->
                    storew e (slot e (arg 0)) (arg 1) >>= bool
                | _ -> Machine.return None))

      (* the thread, whose function returned to [exit_addr], exits with
         its result *)
      let returned e addr =
        if (not (Poly.equal e.arch Uc.X86)) || Int64.(addr <> exit_addr) then
          Machine.return None
        else
          is_pe >>= function
          | false -> Machine.return None
          | true ->
              let* () = pull e in
              let* st = Machine.Local.get threads in
              exit_thread e st (get e (result e))
    end

    (* the threads, that [spawn] created, return to [exit_addr], which
       is not mapped, also on the other targets *)
    let exit_addr = Windows.exit_addr

    (* the thread, that the script creates, see [Bap_emu.spawn_thread],
       which calls [start] with [arg], on the [stack], whose top is the
       address, or on the new one, of 256 KB, and exits, when [start]
       returns, with its result, and is the TID of the thread, on the
       targets, whose threads Linux or Windows create *)
    let spawn e ~start ~arg ~stack =
      (* the function of Thumb, whose symbol has the lower bit *)
      let start =
        if
          Poly.equal e.arch Arm
          && Int64.(start land 1L = 0L)
          && Hash_set.mem e.session.thumb (word e start)
        then Int64.(start lor 1L)
        else start
      in
      let* st = Machine.Local.get threads in
      if too_many_threads st then fail "too many threads"
      else
        Windows.is_pe >>= function
        | true ->
            let+ _ =
              Windows.create e st ~start ~param:arg ~size:0L ~suspended:false
            in
            st.last + 1
        | false -> (
            match abi e with
            | None -> fail "the threads of the target are not supported"
            | Some abi ->
                let tid = st.last + 1 in
                let* top =
                  match stack with
                  | Some top -> Machine.return Int64.(top land lnot 15L)
                  | None ->
                      let size = 0x40000 in
                      let+ base = Windows.allocate e size in
                      Int64.(base + of_int size)
                in
                (* the return address is on the stack on x86, with the
                   argument after it on x86, at the entry of the function,
                   whose stack is aligned before the call, and else in the
                   link register, and the stack has the space, that the
                   callee may use, e.g., of the arguments of MIPS *)
                let* sp =
                  match (e.arch, e.link) with
                  | X86, _ when e.bytes = 8 ->
                      let sp = Int64.(top - 8L) in
                      let+ _ = storew e sp exit_addr in
                      sp
                  | X86, _ ->
                      let sp = Int64.(top - 0x14L) in
                      let* _ = storew e sp exit_addr in
                      let+ _ = storew e Int64.(sp + 4L) arg in
                      sp
                  | _ -> Machine.return Int64.(top - 64L)
                in
                let first = List.hd abi.args in
                let* () =
                  copy e tid ~changed:(fun v x ->
                      let name = Var.name v in
                      if Var.equal v e.sp then like x sp
                      else if
                        Option.exists e.link ~f:(Var.equal v)
                        && not (Poly.equal e.arch X86)
                      then like x exit_addr
                      else if
                        (not (Poly.equal e.arch X86 && e.bytes = 4))
                        && Option.equal String.equal first (Some name)
                      then like x arg
                        (* the PIC code of MIPS finds its GOT from T9,
                           which is the address of the function *)
                      else if Poly.equal e.arch Mips && String.equal name "R25"
                      then like x Int64.(start land lnot 1L)
                      else Machine.return x)
                in
                let child =
                  {
                    tid;
                    saved_extra =
                      List.map (extra e) ~f:(fun id -> (id, read_extra e id));
                    next = start;
                    wait = Ready;
                    clear = None;
                    woken = false;
                  }
                in
                let+ () =
                  Machine.Local.put threads
                    {
                      st with
                      others = st.others @ [ child ];
                      last = tid;
                      depth =
                        Some
                          (Option.value st.depth ~default:(List.length e.frames));
                    }
                in
                tid)

    (* the thread, whose function returned to [exit_addr], exits with
       its result, see [spawn] *)
    let returned e addr =
      Windows.returned e addr >>= function
      | Some pc -> Machine.return (Some pc)
      | None -> (
          if Int64.(addr <> exit_addr) then Machine.return None
          else
            match abi e with
            | None -> Machine.return None
            | Some abi ->
                let* () = pull e in
                let* st = Machine.Local.get threads in
                if st.current = 1 then Machine.return None
                else exit_thread e st (get e abi.result))
  end

  (* the instruction at [pc], which Primus interprets after the one it
     interpreted, as it uses a tracked register, or the memory, while a
     location is tracked, unless it is a stop of the run, e.g., the
     return of the run, a trampoline, a stop of Primus, or the entry of a
     function, whose calls the script hooks *)
  let continues e pc =
    let addr = code_addr e pc in
    if
      Hashtbl.mem e.trampolines addr
      || Hash_set.mem e.foreign addr
      || is_stop e addr
      (* the hooks of the calls run in Unicorn, see [call_returns] *)
      || Option.exists (function_name e addr)
           ~f:(Hashtbl.mem e.session.call_hooks)
      || Option.equal Int64.equal e.session.checkpoint_addr (Some addr)
      || (e.session.driven && e.session.pause)
      ||
      match e.frames with
      | { ret; _ } :: _ -> Int64.(ret = addr)
      | [] -> false
    then Machine.return false
    else
      let* { uses; memory; _ } = analyze ~thumb:(in_thumb e pc) e addr in
      if List.exists uses ~f:(Hash_set.mem e.tracked) then Machine.return true
      else if memory && not e.shadowing then Track.has_marks
      else Machine.return false

  (* the loads and the stores of the atomic sequences, e.g., ldrex and
     strex of ARM, lwarx and stwcx. of PowerPC, ll and sc of MIPS, by the
     names of their instructions *)
  let load_linked name =
    List.exists
      [
        "LDREX";
        "LDAEX";
        "LDXR";
        "LDAXR";
        "LDXP";
        "LDAXP";
        "LBARX";
        "LHARX";
        "LWARX";
        "LDARX";
        "LR_";
        (* LL_R6 and LLD_R6 of the release 6 of MIPS *)
        "LL_";
        "LLD_";
      ] ~f:(fun prefix -> String.is_prefix name ~prefix)
    || List.mem [ "LL"; "LLD"; "LL64"; "LLD64" ] name ~equal:String.equal

  let store_conditional name =
    List.exists
      [
        "STREX";
        "STLEX";
        "STXR";
        "STLXR";
        "STXP";
        "STLXP";
        "STBCX";
        "STHCX";
        "STWCX";
        "STDCX";
        "SC_";
        "SCD_";
      ] ~f:(fun prefix -> String.is_prefix name ~prefix)
    || List.mem [ "SC"; "SCD"; "SC64"; "SCD64" ] name ~equal:String.equal

  (* Primus interprets the instructions from [pc], see [trace], while
     they continue, see [continues], and returns the address of the next
     one, which on ARM stays in the Thumb state, unless the jump sets the
     lower bit *)
  let interpret ?(budget = 4096) ?(slot = true) ?(strict = true) e pc =
    let* () = pull e in
    let* pc = if slot then branch_of_slot e pc else Machine.return pc in
    (* the call of the threads runs in Unicorn, see [Threads] *)
    let threads_call site =
      match Threads.abi e with
      | None -> Machine.return false
      | Some { number; _ } ->
          let+ n = Env.get (Var.create number (Type.imm (e.bytes * 8))) in
          Threads.is_call e site (int64_of_word (Primus.Value.to_word n))
    in
    let stopped = ref false and linked = ref false in
    let rec run pc n =
      let insn = pc in
      lift ~thumb:(in_thumb e pc) e (code_addr e pc) >>= function
      | None -> unrunnable e pc "can't interpret the instruction"
      (* the instruction, that Unicorn left to Primus, e.g., as it
         accessed the tainted memory, has the semantics, else it would
         run again and again *)
      | Some (_, blks)
        when strict && n = budget
             && List.for_all blks ~f:(fun blk ->
                 Term.length def_t blk = 0 && Term.length jmp_t blk = 0) ->
          fail "the instruction at %Lx has no semantics to interpret" pc
      | Some (size, blks) ->
          let next = Int64.(pc + of_int size) in
          let* pc =
            match site_of_blocks blks with
            | Some site -> (
                threads_call site >>= function
                | true ->
                    stopped := true;
                    Machine.return pc
                | false ->
                    (* the intrinsics run, as the interpreter calls them
                       by their names, and the instruction continues after
                       them, e.g., it moves their results *)
                    let next = word e (code_addr e next) in
                    let+ dst = Interpreter.step ~next blks in
                    int64_of_word (Primus.Value.to_word dst))
            | None -> (
                let next = word e (code_addr e next) in
                match e.arch with
                | Arm ->
                    (* the mode, that the jump enters, see [Interworking] *)
                    let blks = Primus.Interworking.unmask blks in
                    let* dst = Interpreter.step ~next blks in
                    let+ name = Lift.name (code_addr e pc) in
                    let name = Option.value name ~default:"" in
                    let dst, thumb =
                      Primus.Interworking.jump ~name ~thumb:(in_thumb e pc)
                        ~next blks (Primus.Value.to_word dst)
                    in
                    let dst = int64_of_word dst in
                    if thumb then Int64.(dst lor 1L) else dst
                | Mips -> (
                    (* the branch, that is taken, runs its delay slot,
                       after its condition and its link, as the lifter
                       lifts the branches without their delay slots, and
                       the compact branch of the release 6 doesn't run
                       the instruction after it, its forbidden slot *)
                    let* dst = Interpreter.step ~next blks in
                    let dst = int64_of_word (Primus.Value.to_word dst) in
                    let slot = Int64.(pc + of_int size) in
                    let delayed =
                      (not e.r6)
                      ||
                      match uc_read e pc 4 with
                      | data -> mips_delayed ~r6:true (word_of_insn e data)
                      | exception (Native.Missing _ | Native.Denied) -> true
                    in
                    if Int64.(dst = slot) || not delayed then Machine.return dst
                    else
                      lift e slot >>= function
                      | None ->
                          fail "can't interpret the delay slot at %Lx" slot
                      | Some (n, blks) ->
                          let next = word e Int64.(slot + of_int n) in
                          let+ _ = Interpreter.step ~next blks in
                          dst)
                | _ ->
                    let+ dst = Interpreter.step ~next blks in
                    int64_of_word (Primus.Value.to_word dst))
          in
          (* the store, that is conditional on the load, that Primus
             interpreted, is interpreted too, as Unicorn has no
             reservation of the load *)
          let* () =
            Lift.name (code_addr e insn) >>| function
            | Some name when load_linked name -> linked := true
            | Some name when store_conditional name -> linked := false
            | _ -> ()
          in
          let* more =
            if n > 1 && not !stopped then
              if !linked then Machine.return true else continues e pc
            else Machine.return false
          in
          if more then run pc (n - 1) else Machine.return pc
    in
    let* pc = run pc budget in
    let+ () = push_owned e in
    fresh e pc;
    pc

  (* The machine, which the script drives, pauses, and serves the
     requests of the script, until it continues. The machine, which
     takes a snapshot, forks, and its parent stays paused, as the
     snapshot, which the script restores, after which the snapshot forks
     again, so that it stays, and its fork continues. The machine, which
     serves, owns Unicorn, as the script accesses its state there. *)
  let rec serve pc =
    let* e = prepare () in
    e.session.pause <- false;
    let* id = Machine.current () in
    match Effect.perform (Paused (pc, id)) with
    | Continue pc -> Machine.return pc
    | Map addr -> ensure_page e addr >>= fun () -> serve pc
    | Interpret -> interpret ~budget:1 ~slot:false ~strict:false e pc >>= serve
    | Set_pc pc -> serve pc
    | Store (addr, data) ->
        (* the stored bytes of a read-only segment would be writable, so
           they keep their protection *)
        let bytes =
          List.init (String.length data) ~f:(fun i ->
              word e Int64.(addr + of_int i))
        in
        let* before = Machine.List.map bytes ~f:Memory.protection in
        let* () = Memory.store_bytes (word e addr) data in
        let* after = Machine.List.map bytes ~f:Memory.protection in
        (* only the changed ones, by their ranges, as each protection
           stays in the memory, and drops the page of Unicorn *)
        let changed =
          List.zip_exn bytes (List.zip_exn before after)
          |> List.filter_map ~f:(function
            | a, (Some p, q)
              when not (Option.equal Primus.Memory.equal_protection (Some p) q)
              ->
                Some (a, p)
            | _ -> None)
        in
        let ranges =
          List.fold changed ~init:[] ~f:(fun acc (a, p) ->
              match acc with
              | (lower, upper, p') :: rest
                when Word.equal (Word.succ upper) a
                     && Primus.Memory.equal_protection p p' ->
                  (lower, a, p) :: rest
              | _ -> (a, a, p) :: acc)
        in
        let* () =
          Machine.List.iter ranges ~f:(fun (lower, upper, p) ->
              Memory.protect ~lower ~upper p)
        in
        serve pc
    | Run component ->
        (* the component sees the state of Unicorn, and its changes go
           there *)
        let* () = pull e in
        let* before = registers e in
        let module Component = (val component : Primus.Machine.Component) in
        let module Component = Component (Machine) in
        let* () = Component.init () in
        (* the component may set the registers without the observations
           of the interpreter, e.g., with [Env.set], so the ones, that it
           changed, go to Unicorn *)
        let* after = registers e in
        let* () =
          push_vars e
            (Map.fold after ~init:[] ~f:(fun ~key ~data acc ->
                 match Map.find before key with
                 | Some x when Word.equal x data -> acc
                 | _ -> key :: acc))
        in
        serve pc
    | Save (file, pc') ->
        let* r = save e pc' file in
        e.session.saved <- r;
        serve pc
    | Spawn (start, arg, stack) ->
        let* r =
          Machine.catch
            (Threads.spawn e ~start ~arg ~stack >>| Result.return)
            (fun exn -> Machine.return (Error (Primus.Exn.to_string exn)))
        in
        e.session.spawned <- r;
        serve pc
    | Snapshot -> pull e >>= fun () -> snapshot id pc
    | Restore snapshot ->
        let* () = Machine.kill id in
        let* () = Machine.switch snapshot in
        (* the killed machine never continues *)
        serve pc

  and snapshot id pc =
    let* () = Machine.fork () in
    let* self = Machine.current () in
    if Monads.Std.Monad.State.Multi.Id.equal self id then snapshot id pc
    else serve pc

  let rec loop pc =
    let* e = prepare () in
    let s = e.session in
    if s.driven && s.pause then (
      (* the thread, that paused, didn't run, so its time slice is
         shifted by the pause, rather than started anew, as a script,
         that pauses it more often than the slice, would starve the
         other threads, and it runs the instruction, at which it paused,
         before it is preempted *)
      let paused = clock () in
      serve pc >>= fun pc ->
      let pause = clock () -. paused in
      s.sliced_at <- s.sliced_at +. pause;
      (* nor does the pause count, as the time, that the machine ran *)
      s.accounted <- s.accounted +. pause;
      (* the program, that paused elsewhere, e.g., after a stub, whose
         call a hook saw, didn't skip a hook, so it may be preempted *)
      s.resumed <- Option.equal Int64.equal s.hooked_at (Some pc);
      s.hooked_at <- None;
      loop pc)
    else
      check_pages e >>= fun () ->
      ensure_page e pc >>= fun () ->
      let* () = account () in
      let* used = Machine.Local.get elapsed in
      let remaining = Option.map s.timeout ~f:(fun t -> t -. used) in
      match remaining with
      | Some t when Float.(t <= 0.) -> terminate e
      | _ -> (
          let* () = sync_stops e in
          let* () = tracking e in
          let* () = watching e in
          (* the time slice of the thread, while the others are ready,
             which ends, however often Unicorn stops, e.g., at each
             load, that the observers see *)
          let* sliced = Machine.Local.get threads >>| Threads.ready e in
          let now = clock () in
          let ends = s.sliced_at +. Threads.slice in
          (* the thread, that a hook of the code paused, runs the
             instruction, at which it paused, before it is preempted *)
          let resumed = s.resumed in
          s.resumed <- false;
          (* the thread doesn't switch in an atomic sequence of the
             lifted engine, see [Uc.in_atomic] *)
          let expired =
            sliced && Float.(now >= ends) && not (Uc.in_atomic e.uc)
          in
          if expired && not resumed then Threads.preempt e pc >>= loop
          else
            let deadline = Option.map remaining ~f:(fun t -> now +. t) in
            let deadline =
              if sliced then
                Some
                  (Float.min
                     (Option.value deadline ~default:Float.infinity)
                     ends)
              else deadline
            in
            (* the thread, whose slice ended, while it was paused, runs
               the instruction, at which it paused, which the hooks saw,
               and is preempted after it *)
            let count = Option.some_if (expired && resumed) 1 in
            (* the one instruction runs without the timeout, whose stop
               would race with the stops of the hooks *)
            let deadline = if Option.is_some count then None else deadline in
            let error = start_uc ?count e pc deadline in
            let* () = account () in
            (* the taint, that the engine changed, goes to Primus, before
               anything sees it, e.g., a script, see [Shadow] *)
            let* () = if e.shadowing then pull_regs e else Machine.return () in
            let* () = observe e in
            let pc = current_pc e in
            (match e.reason with
            | Some (Fault _ | Unknown _)
              when Option.equal Int64.equal s.skipped_at (Some (code_addr e pc))
              ->
                s.resumed_at <- s.skipped_at
            | _ -> ());
            match (e.reason, error) with
            | None, None when sliced && not (Uc.in_atomic e.uc) ->
                Threads.preempt e pc >>= loop
            | None, None when Option.is_some remaining -> loop pc
            | Some Returned, _ | None, None -> pull e
            | Some (Foreign addr), _ -> (
                let addr = trampoline e addr in
                match
                  Option.bind (function_name e addr) ~f:(call_returns e)
                with
                | Some pc -> loop pc
                | None -> (
                    (* the functions of the threads of Windows, see
                       [Threads.Windows] *)
                    Threads.Windows.call e addr
                    >>= function
                    | Some pc -> loop pc
                    | None -> (
                        native e addr >>= function
                        | Some pc -> loop pc
                        | None -> call_foreign e addr >>= loop)))
            | Some Pause, _ ->
                s.hooked_at <- Some pc;
                loop pc
            | Some Interrupted, _ -> loop pc
            | Some (Observe _), _ ->
                let* () =
                  Machine.Observation.observed Primus.Interpreter.pc_change
                  >>= function
                  | false -> Machine.return ()
                  | true ->
                      let* () = pull e in
                      let* () = Interpreter.set_pc (word e (code_addr e pc)) in
                      push_owned e
                in
                loop pc
            | Some (Jump pc), _ -> loop pc
            | Some (Fault (access, addr)), _ -> (
                Threads.returned e addr >>= function
                | Some pc -> loop pc
                | None -> (
                    fault e access addr >>= function
                    | `Continue -> loop pc
                    | `Interpret -> interpret e pc >>= loop))
            | Some (Interpret _), _ -> interpret e pc >>= loop
            | Some (Unknown addr), _ ->
                analyze ~thumb:(in_thumb e pc) e addr >>= fun _ -> loop pc
            | Some (Interrupt n), _ -> (
                let* () = Interpreter.interrupt n in
                let thumb = Int64.(pc land 1L = 1L) in
                let* read = code_reader e (code_addr e pc) in
                let encoding = arm_encoding e ~thumb:(in_thumb e pc) in
                trap ~read ?encoding e.arch ~thumb n (code_addr e pc)
                >>= function
                | Some (site, next) -> (
                    let next = if thumb then Int64.(next lor 1L) else next in
                    Threads.syscall e ~next >>= function
                    | Some pc -> loop pc
                    | None -> call_intrinsic e site >>= fun () -> loop next)
                | None ->
                    pull e >>= fun () ->
                    fail "an unhandled interrupt %d at %Lx" n pc)
            | Some Checkpoint, _ -> (
                s.checkpointed <- true;
                let file, _ = Option.value_exn s.checkpoint in
                save e pc file >>= fun saved ->
                match saved with Ok () -> loop pc | Error msg -> fail "%s" msg)
            | Some (Stop addr), _ -> stopped e addr >>= fun () -> loop pc
            | Some Invalid, _ ->
                pull e >>= fun () -> unrunnable e pc "an invalid instruction"
            | None, Some msg -> pull e >>= fun () -> fail "%s at %Lx" msg pc)

  (* the stop, at which the observers of the stops, e.g., a debugger,
     see the state of the machine, and may change it, after
     which Unicorn continues from the address *)
  and stopped e addr =
    let* () = pull e in
    let* () = Interpreter.set_pc (word e addr) in
    let+ () = push_owned e in
    e.session.resumed_at <- Some addr

  let start e addr =
    let pc = int64_of_word addr in
    match e.arch with
    | Arm when Hash_set.mem e.session.thumb addr -> Int64.(pc lor 1L)
    | _ -> pc

  (* the states of the components, that extend the checkpoint, see
     [Primus.Checkpoint] *)
  let restore_extensions (cp : Checkpoint.t) =
    Machine.List.iter cp.extensions ~f:(fun (name, data) ->
        match Primus.Checkpoint.find name with
        | Some (module Ext) ->
            let module Ext = Ext (Machine) in
            Ext.restore data
        | None ->
            warning "the state of %s is not restored, as it is not loaded" name;
            Machine.return ())

  (* the stub, that called the function of the run, which returned,
     completes, if it is known, see [Completion] *)
  let completed ({ callee; caller; _ } : Checkpoint.frame) =
    match caller with
    | None -> Machine.return ()
    | Some stub -> (
        match Hashtbl.find completions stub with
        | Some (module C) ->
            let module C = C (Machine) in
            C.complete ~callee
        | None ->
            info
              "the run of %s returned to %s, which the checkpoint doesn't have"
              (Option.value callee ~default:"the code")
              stub;
            Machine.return ())

  (* the run continues from the checkpoint, and ends when it returns,
     see [Checkpoint] *)
  let resume (cp : Checkpoint.t) =
    let* () = Machine.Local.put restored true in
    let* () = Memory.restore cp.memory in
    let* () =
      Machine.List.iter cp.vars ~f:(fun (v, x) -> Value.of_word x >>= Env.set v)
    in
    let* () = restore_extensions cp in
    let* e = engine () in
    let* id = Machine.current () in
    (* the memory of the machine is replaced, and the parked pages of
       another machine, that owns Unicorn, are kept *)
    if not (is_owner e id) then park e;
    forget e;
    unpark_all e.session id;
    e.owner <- Some id;
    let* () = map_code e in
    let* () = push e in
    List.iter cp.extra ~f:(fun (id, data) -> write_extra e id data);
    let* () = sync_stops e in
    (let addr = code_addr e cp.pc in
     if
       Option.equal Int64.equal e.session.checkpoint_addr (Some addr)
       || is_stop e addr
     then e.session.resumed_at <- Some addr);
    info "continues from the checkpoint at %Lx" cp.pc;
    match cp.frames with
    | [] -> fail "the checkpoint has no run"
    | ({ ret; sp; callee; caller } as top) :: _ ->
        let* pending = Machine.Local.get frames in
        let* called = Machine.Local.get calls in
        let* () = Machine.Local.put frames ({ ret; sp } :: pending) in
        let* () = Machine.Local.put calls ((callee, caller) :: called) in
        (* the threads switch in the run, that continues *)
        let* () =
          match cp.threads with
          | None -> Machine.return ()
          | Some { current; cleared; others; last; woken } ->
              Machine.Local.put threads
                {
                  current;
                  cleared;
                  last;
                  woken;
                  depth = Some (List.length pending + 1);
                  others =
                    List.map others
                      ~f:(fun { tid; extra; next; waiting; clear; woken } ->
                        {
                          tid;
                          saved_extra = extra;
                          next;
                          clear;
                          woken;
                          wait =
                            (match waiting with
                            | None -> Ready
                            | Some addrs -> Waiting addrs);
                        });
                }
        in
        let* () = loop cp.pc in
        let* () = Machine.Local.put frames pending in
        let* () = Machine.Local.put calls called in
        completed top

  (* the slots of the external functions refer to their trampolines in
     Primus too, as the code, that Primus interprets, see [interpret],
     calls them through the slots *)
  let link_slots e =
    let* linked = Machine.Local.get slotted in
    if linked then Machine.return ()
    else
      let* () = Machine.Local.put slotted true in
      Hashtbl.to_alist e.slots
      |> Machine.List.iter ~f:(fun (page, slots) ->
          Machine.List.iter slots ~f:(fun (off, addr) ->
              let data =
                String.init e.bytes ~f:(fun i ->
                    let shift = if e.big_endian then e.bytes - 1 - i else i in
                    Char.of_int_exn
                      Int64.(
                        to_int_exn
                          (shift_right_logical addr Int.(8 * shift) land 0xFFL)))
              in
              Memory.store_bytes (word e Int64.(page + of_int off)) data))

  let run addr =
    let* e = engine () in
    let* () = link_slots e in
    let* restored = Machine.Local.get restored in
    match e.session.restored_from with
    | Some cp when not restored -> resume cp
    | _ ->
        let* e = engine () in
        let* claimed = claim e in
        let* () = if claimed then map_code e else Machine.return () in
        let* () = push e in

        let* frame = frame e in
        let* pending = Machine.Local.get frames in
        let* called = Machine.Local.get calls in
        let* stubs = Machine.Local.get lisp_calls in
        let callee = Hashtbl.find e.session.names (int64_of_word addr) in
        let* () =
          Machine.Local.put frames
            ({ frame with ret = address e frame } :: pending)
        in
        let* () = Machine.Local.put calls ((callee, List.hd stubs) :: called) in
        let* () = loop (start e addr) in
        let* () = Machine.Local.put frames pending in
        Machine.Local.put calls called
end

(* __libc_start_main exits with the result of main, see its Lisp stub,
   as the result of a function is in its output argument, see its
   prototype, otherwise where the C ABI returns a word, as the Lisp
   primitive invoke-subroutine takes it *)
module Exit (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Interpreter = Primus.Interpreter.Make (Machine)
  module Lisp = Primus.Lisp.Make (Machine)

  let result target signature =
    match signature with
    | Some { output = Some (exp, _); _ } -> Some exp
    | _ -> (
        match Bap_c.Std.C.Abi.lookup target with
        | None -> None
        | Some abi ->
            let proto : Bap_c.Std.C.Type.proto =
              {
                return = Bap_c.Std.C.Type.basic `sint;
                args = [];
                variadic = false;
              }
            in
            Bap_c.Std.C.Abi.apply abi
              (Bap_c.Std.C.Abi.model target)
              [] proto (Sub.create ())
            |> Term.enum arg_t
            |> Seq.find_map ~f:(fun arg ->
                match Arg.intent arg with
                | Some Out -> Some (Arg.rhs arg)
                | _ -> None))

  let complete ~callee =
    Machine.Global.get session_state >>= fun s ->
    Machine.gets Project.target >>= fun target ->
    let signature = Option.bind callee ~f:(Hashtbl.find s.signatures) in
    match result target signature with
    | None -> Machine.return ()
    | Some exp ->
        Interpreter.exp exp >>= fun code ->
        Lisp.eval_fun "exit" [ code ] >>| ignore
end

let () = complete "__libc_start_main" (module Exit)

(* the time, that the machine has run, which its timeout limits *)
module Elapsed (Machine : Primus.Machine.S) = struct
  open Machine.Syntax

  let save = Machine.Local.get elapsed >>| fun t -> Some (Float.to_string t)

  (* the time is finite, and not negative, so that it doesn't disable the
     timeout, e.g., in a checkpoint, that is crafted *)
  let restore data =
    Machine.Local.put elapsed
      (match Float.of_string_opt data with
      | Some t when Float.is_finite t && Float.(t >= 0.) -> t
      | _ -> 0.)
end

let () =
  Primus.Checkpoint.register ~package:"bap" "unicorn-elapsed" (module Elapsed)

(* links the program, as load-binary does, except that its subroutines
   run in Unicorn, and keeps the linked code to tell the addresses of the
   subroutines that other components replace *)
(* The engine of the new sessions of the system, which the component
   bap:lifted-emulator of the lifted executors chooses, see
   [Lifted_emulator], while the scripts choose the engines of theirs, see
   [Bap_emu.create].

   The components initialize in the order of the hashes of their names,
   see [Primus.System], so the executors share the loader, whose place in
   the order is tested, and the name of the component, that chooses the
   engine, is before it, which the loader checks, see [chosen]. *)
let engine_kind =
  Primus.Machine.State.declare ~uuid:"0e5d8a3c-6f21-4b9e-9c47-3a1f2d8e7b60"
    ~name:"executor-engine" (fun _ -> (`Unicorn : kind))

(* the engine, that the loader chose for its new session *)
let chosen =
  Primus.Machine.State.declare ~uuid:"5b7c2e19-8d4a-4f63-a1e0-9c6b3d2f8a47"
    ~name:"executor-engine-chosen" (fun _ -> (None : kind option))

module Lifted_emulator (Machine : Primus.Machine.S) = struct
  let init () = Machine.Global.put engine_kind `Lifted
end

module Loader (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  open Machine.Let
  module Linker = Primus.Linker.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)

  let is_linked name t =
    let* linked =
      Machine.List.exists
        [ `tid (Term.tid t); `symbol (name t) ]
        ~f:Linker.is_linked
    in
    if linked then Machine.return true
    else
      match Term.get_attr t address with
      | None -> Machine.return false
      | Some addr -> Linker.is_linked (`addr addr)

  let link_blk blk =
    let* linked = is_linked Term.name blk in
    if linked then Machine.return ()
    else
      let module Code (Machine : Primus.Machine.S) = struct
        module Interp = Primus.Interpreter.Make (Machine)

        let exec = Interp.blk blk
      end in
      Linker.link ~name:(Term.name blk) ~tid:(Term.tid blk)
        ?addr:(Term.get_attr blk address)
        (module Code)

  (* the native functions, whose arguments are evaluated in Unicorn, and
     whose result is written to a register, see [Make.eval_uc] *)
  let index_natives s prog =
    Term.enum sub_t prog
    |> Seq.iter ~f:(fun sub ->
        let name = Sub.name sub in
        Option.iter (Term.get_attr sub address) ~f:(fun addr ->
            Hashtbl.set s.names ~key:(int64_of_word addr) ~data:name);
        let args = Term.enum arg_t sub |> Seq.to_list in
        match args with
        | [] -> ()
        | _ ->
            let args = args in
            let outs, ins =
              List.partition_tf args ~f:(fun arg ->
                  match Arg.intent arg with Some Out -> true | _ -> false)
            in
            let width arg =
              match Var.typ (Arg.lhs arg) with Imm n -> Some n | _ -> None
            in
            let assignable (exp : exp) =
              match exp with
              | Var _ | Cast (LOW, _, Var _) | Extract (_, 0, Var _) -> true
              | _ -> false
            in
            let signature =
              match outs with
              | [] -> Some { inputs = List.map ins ~f:Arg.rhs; output = None }
              | [ out ] when assignable (Arg.rhs out) ->
                  Option.map (width out) ~f:(fun n ->
                      {
                        inputs = List.map ins ~f:Arg.rhs;
                        output = Some (Arg.rhs out, n);
                      })
              | _ -> None
            in
            Option.iter signature ~f:(fun { inputs; output } ->
                Hashtbl.set s.signatures ~key:name ~data:{ inputs; output };
                match Native.find name with
                | Some fn
                  when Set.mem s.native_stubs name && not (List.is_empty inputs)
                  ->
                    Hashtbl.set s.natives ~key:name
                      ~data:{ fn; args = inputs; result = output }
                | _ -> ()))

  let link_sub s sub =
    let* linked = is_linked Sub.name sub in
    if linked then Machine.return ()
    else
      match Term.get_attr sub address with
      | None ->
          (* the subs of the bare project are synthetic, their terms have
             no code and their arg terms must not be evaluated; what is
             not replaced, e.g., by the Lisp stubs, is unresolved *)
          if s.bare_mode then Machine.return ()
          else
            let module Code (Machine : Primus.Machine.S) = struct
              module Interp = Primus.Interpreter.Make (Machine)

              let exec = Interp.sub sub
            end in
            Linker.link ~name:(Sub.name sub) ~tid:(Term.tid sub) (module Code)
      | Some addr ->
          let module Code (Machine : Primus.Machine.S) = struct
            module Exec = Make (Machine)

            let exec = Exec.run addr
          end in
          let code : Primus.Linker.code = (module Code) in
          Hashtbl.set s.own_code ~key:addr ~data:code;
          if Term.has_attr sub Sub.stub then begin
            let module Stub (Machine : Primus.Machine.S) = struct
              module Interp = Primus.Interpreter.Make (Machine)

              let exec = Interp.sub sub
            end in
            Hashtbl.set s.stubs ~key:addr ~data:(module Stub)
          end;
          if is_thumb s sub then Hash_set.add s.thumb addr;
          Linker.link ~addr ~name:(Sub.name sub) ~tid:(Term.tid sub) code

  let link_program s =
    let* prog = Machine.gets Project.program in
    index_natives s prog;
    Term.enum sub_t prog |> Seq.to_list
    |> Machine.List.iter ~f:(fun sub ->
        let* () = link_sub s sub in
        Term.enum blk_t sub |> Seq.to_list |> Machine.List.iter ~f:link_blk)

  (* the code at an address, that nothing is linked to, e.g., of a
     function of the stripped program, runs in Unicorn, from the address
     without the lower bit in the Thumb state of ARM *)
  let session = Machine.Global.get session_state

  let link_unresolved : Primus.Linker.name -> unit Machine.t = function
    | `addr addr ->
        let* s = session in
        let* proj = Machine.get () in
        let start =
          match Project.arch proj with
          | (#Arch.arm | #Arch.thumb)
            when Word.(is_one (extract_exn ~hi:0 addr)) ->
              let start = Word.(addr - one (bitwidth addr)) in
              Hash_set.add s.thumb start;
              start
          | _ -> addr
        in
        let* executable = Memory.is_executable start in
        if not executable then Machine.return ()
        else
          let module Code (Machine : Primus.Machine.S) = struct
            module Exec = Make (Machine)

            let exec = Exec.run start
          end in
          Linker.link ~addr (module Code)
    | `symbol _ | `tid _ -> Machine.return ()

  (* the references to the external functions of the program *)
  let externals s =
    let* proj = Machine.get () in
    (* the bare project has subroutines for all imports, e.g., of the
       data objects, so the functions there are those, that the
       components, e.g., the Lisp machine, link, e.g., the stubs *)
    let* functions =
      if s.bare_mode then Linker.linked_symbols >>| String.Set.of_list
      else
        Machine.return
          (Term.enum sub_t (Project.program proj)
          |> Seq.map ~f:Sub.name |> Seq.to_list |> String.Set.of_list)
    in
    let is_function = Set.mem functions in
    match
      Ogre.eval
        (Ogre.collect
           Ogre.Query.(select (from Image.Scheme.external_reference)))
        (Project.specification proj)
    with
    | Error _ -> Machine.return []
    | Ok refs ->
        (* some loaders refer to the code, e.g., to the PLT entries, which
           are not the slots, but the slots of GOT are, also in the segment,
           that is writable and executable, e.g., of the code, that the
           program writes, which has the data too *)
        let width = Theory.Target.code_addr_size (Project.target proj) in
        let is_code addr =
          let tags =
            Memmap.lookup (Project.memory proj) (Word.of_int64 ~width addr)
            |> Seq.map ~f:snd |> Seq.to_list
          in
          List.exists tags ~f:(fun tag ->
              match Bap.Std.Value.get Image.segment tag with
              | Some seg -> Image.Segment.is_executable seg
              | None -> false)
          && not
               (List.exists tags ~f:(fun tag ->
                    match Bap.Std.Value.get Image.section tag with
                    | Some name -> String.is_prefix name ~prefix:".got"
                    | None -> false))
        in
        (* the slot, that is null in the file, of a function, that
           nothing links, e.g., the weak one, that nothing defines, stays
           null, as the programs test it, e.g., __gmon_start__ *)
        let* linked = Linker.linked_symbols >>| String.Set.of_list in
        let is_null addr =
          let addr = Word.of_int64 ~width addr in
          Memmap.lookup (Project.memory proj) addr
          |> Seq.exists ~f:(fun (mem, _) ->
              match
                Bap.Std.Memory.get ~addr ~scale:(Size.of_int_exn width) mem
              with
              | Ok x -> Word.is_zero x
              | Error _ -> false)
        in
        Machine.return @@ Seq.to_list
        @@ Seq.filter refs ~f:(fun (addr, name) ->
            is_function name
            && (not (is_code addr))
            && (Set.mem linked name || not (is_null addr)))

  (* the address, or the name of the subroutine, as its address *)
  let resolve point =
    match Int64.of_string point with
    | addr -> Machine.return addr
    | exception _ -> (
        let* prog = Machine.gets Project.program in
        let sub =
          Term.enum sub_t prog
          |> Seq.find ~f:(fun sub -> String.equal (Sub.name sub) point)
        in
        match Option.bind sub ~f:(fun sub -> Term.get_attr sub address) with
        | Some addr -> Machine.return (int64_of_word addr)
        | None ->
            Machine.raise
              (Unicorn_failure
                 (sprintf "the checkpoint is at %s, which is not found" point)))

  let load_checkpoint s target =
    let* program = Machine.gets (fun proj -> Project.get proj filename) in
    (* the program, which the checkpoint is of, has the same digest *)
    let same digest =
      match program with
      | None -> true
      (* the checkpoint of the file has its digest *)
      | Some file -> (
          (not (String.is_empty digest))
          &&
            try String.equal digest (Checkpoint.digest file)
            with Sys_error _ -> true)
    in
    match s.restore with
    | None -> Machine.return None
    | Some file -> (
        match Checkpoint.load file with
        | Error msg -> Machine.raise (Unicorn_failure msg)
        | Ok cp when not (same cp.digest) ->
            Machine.raise
              (Unicorn_failure
                 (sprintf "the checkpoint %s is of another program" file))
        | Ok cp when String.equal cp.target (Theory.Target.to_string target) ->
            Machine.return (Some cp)
        | Ok cp ->
            Machine.raise
              (Unicorn_failure
                 (sprintf "the checkpoint %s is of the target %s" file cp.target))
        )

  (* the subroutines, whose code the other components replaced, stop
     Unicorn *)
  let create_engine () =
    let* s = session in
    let* target = Machine.gets Project.target in
    let* () =
      match s.checkpoint with
      | None -> Machine.return ()
      | Some (_, point) ->
          let+ addr = resolve point in
          s.checkpoint_addr <- Some addr
    in
    let* cp = load_checkpoint s target in
    s.restored_from <- cp;
    (* the names and the functions, that the script changed, are of the
       checkpoint too *)
    Option.iter cp ~f:(fun (cp : Checkpoint.t) ->
        List.iter cp.symbols ~f:(fun (name, addr) ->
            Hashtbl.set s.symbols ~key:addr ~data:name);
        List.iter cp.unstubbed ~f:(Hash_set.add s.unstubbed));
    Hashtbl.iteri s.symbols ~f:(fun ~key ~data ->
        Hashtbl.set s.names ~key ~data);
    let* () =
      let module Exec = Make (Machine) in
      Hash_set.to_list s.unstubbed |> Machine.List.iter ~f:Exec.unstub
    in
    let* foreign =
      Hashtbl.keys s.own_code
      |> Machine.List.filter_map ~f:(fun addr ->
          Linker.lookup (`addr addr) >>| function
          | Some code when phys_equal code (Hashtbl.find_exn s.own_code addr) ->
              None
          | _ -> Some (int64_of_word addr))
    in
    (match s.active with Some e -> Uc.close e.uc | None -> ());
    s.active <- None;
    let* externals = externals s in
    s.recipe <- Some (target, foreign, externals);
    let* () =
      if s.lifted && Option.is_none s.lifter then (
        Machine.get () >>| fun proj ->
        let target = Project.target proj in
        let engine = Target.engine target in
        (* the lifted instructions of the program, see [Lifts] *)
        let cache =
          Option.bind s.cache ~f:(fun dir ->
              Option.map (Project.get proj filename) ~f:(fun file ->
                  let program =
                    try Checkpoint.digest file with Sys_error _ -> file
                  in
                  let key =
                    Stdlib.Digest.to_hex
                      (Stdlib.Digest.string
                         (String.concat ~sep:"\000"
                            [
                              s.digest; program; Theory.Target.to_string target;
                            ]))
                  in
                  mkdirs (dir ^/ "lifts") ^/ key ^ ".lifts"))
        in
        let ({ lift; cached; _ } as l) =
          lifter ?cache
            ~arm:(Poly.equal (Option.map engine ~f:fst) (Some Uc.Arm))
            proj
        in
        s.lifter <- Some l;
        (* the first instruction, that is lifted, loads the semantics of
           Primus Lisp, which takes a second or two, so it is lifted now,
           before the program runs, rather than as it runs, e.g., while
           the timer of a script, that stops it, runs *)
        if not cached then
          Option.iter engine ~f:(fun (arch, _) ->
              ignore
                (lift ~thumb:false 0L
                   (nop arch
                      ~big_endian:
                        Theory.Endianness.(
                          equal eb (Theory.Target.endianness target)))
                  : _ option)))
      else Machine.return ()
    in
    match create s target ~foreign ~externals with
    | exception Unsupported msg -> Machine.raise (Unicorn_failure msg)
    | e ->
        s.active <- Some e;
        (* the time of the timeout starts, when the engine is created, as
           the lifter of the lifted engine loads the semantics of Primus
           Lisp then, which isn't the time, that the machine runs *)
        s.accounted <- clock ();
        Hashtbl.clear s.parked;
        s.parked_pages <- 0;
        Memory.set_backing
          (Some (backing s (Theory.Var.name (Theory.Target.data target))))

  (* the session, that the script created for the system, see
     [Bap_emu.create], or a new one *)
  let start_session =
    let* proj = Machine.get () in
    let* s =
      match
        Option.bind
          (Project.get proj session_tag)
          ~f:(Hashtbl.find_and_remove sessions)
      with
      | Some s -> Machine.return s
      | None ->
          let* engine = Machine.Global.get engine_kind in
          let+ () = Machine.Global.put chosen (Some engine) in
          create_session ~engine ()
    in
    s.bare_mode <- not (Project.disassembled proj);
    index_thumb_symbols s (Project.specification proj);
    let* () = Machine.Global.put session_state s in
    link_program s

  (* the component, that chose the engine, initialized before the
     loader, see [engine_kind] *)
  let check_engine () =
    let* engine = Machine.Global.get engine_kind in
    Machine.Global.get chosen >>= function
    | Some chosen when not (Poly.equal chosen engine) ->
        Machine.raise
          (Unicorn_failure
             "the engine was chosen after the loader started, as the order of \
              the components of Primus changed")
    | _ -> Machine.return ()

  (* the intrinsics of x86, see [X86_intrinsics], and the counters of
     RISC-V, unless the program, e.g., Primus Lisp, defines them, which
     compute their results from their inputs, intrinsic:x0, ..., to
     intrinsic:y0 *)
  let link_intrinsics () =
    let* target = Machine.gets Project.target in
    let word w x = Word.of_int64 ~width:w x in
    let intrinsic name ~inputs ~compute =
      Linker.is_linked (`symbol name) >>= function
      | true -> Machine.return ()
      | false ->
          let module Code (Machine : Primus.Machine.S) = struct
            module Env = Primus.Env.Make (Machine)
            module Value = Primus.Value.Make (Machine)
            open Machine.Syntax

            let arg (n, w) =
              Env.get (Var.create (sprintf "intrinsic:x%d" n) (Type.imm w))
              >>| fun x -> Word.to_int64_exn (Primus.Value.to_word x)

            let exec =
              Machine.List.map inputs ~f:arg >>= fun args ->
              match compute args with
              | Ok x ->
                  Value.of_word x
                  >>= Env.set
                        (Var.create "intrinsic:y0" (Type.imm (Word.bitwidth x)))
              | Error what ->
                  Machine.raise
                    (Unicorn_failure (sprintf "%s faults in Unicorn" what))
          end in
          Linker.link ~name (module Code)
    in
    let words ws =
      List.reduce_exn (List.rev ws) ~f:(fun hi lo -> Word.concat hi lo)
    in
    match Target.engine target with
    | Some (X86, mode) ->
        let* () =
          intrinsic "intrinsic:cpuid"
            ~inputs:[ (0, 32); (1, 32) ]
            ~compute:(function
              | [ a; c ] -> (
                  match X86_intrinsics.run mode "\x0f\xa2" a c with
                  | Some regs -> Ok (words (List.map regs ~f:(word 32)))
                  | None -> Error "cpuid")
              | _ -> Error "cpuid")
        in
        let* () =
          intrinsic "intrinsic:xgetbv"
            ~inputs:[ (0, 32) ]
            ~compute:(function
              | [ c ] -> (
                  match X86_intrinsics.run mode "\x0f\x01\xd0" 0L c with
                  | Some [ eax; _; _; edx ] ->
                      Ok (words [ word 32 eax; word 32 edx ])
                  | _ -> Error "xgetbv")
              | _ -> Error "xgetbv")
        in
        let* () =
          intrinsic "intrinsic:rdtsc" ~inputs:[] ~compute:(fun _ ->
              Ok (word 64 (X86_intrinsics.tsc ())))
        in
        (* the TSC_AUX of RDTSCP, the number of the processor, is 0 *)
        intrinsic "intrinsic:rdtscp" ~inputs:[] ~compute:(fun _ ->
            Ok (words [ word 64 (X86_intrinsics.tsc ()); word 32 0L ]))
    | Some (Riscv, _) ->
        (* the cycles and the instructions are the nanoseconds of the
           clock, and the time is of the timebase of 10 MHz, as of the
           virt machine of QEMU *)
        let bits = Theory.Target.bits target in
        let counter name scale =
          intrinsic name ~inputs:[] ~compute:(fun _ ->
              Ok (word bits Int64.(X86_intrinsics.tsc () / scale)))
        in
        let* () = counter "intrinsic:riscv_csr_cycle" 1L in
        let* () = counter "intrinsic:riscv_csr_instret" 1L in
        counter "intrinsic:riscv_csr_time" 100L
    | _ -> Machine.return ()

  let init () =
    let module Exec = Make (Machine) in
    Machine.sequence
      [
        start_session;
        Primus.System.init >>> link_intrinsics;
        Primus.System.init >>> check_engine;
        Primus.System.init >>> create_engine;
        Primus.Machine.fork >>> Exec.forked;
        Primus.Linker.unresolved >>> link_unresolved;
        ( Primus.Interpreter.exited >>> fun code ->
          let+ s = session in
          s.exit_code <-
            Some
              (Word.to_int_exn
                 (Word.extract_exn ~hi:7 (Primus.Value.to_word code))) );
        Primus.Machine.kill >>> Exec.killed;
        Primus.System.fini >>> Exec.finished;
        Primus.System.stop >>> Exec.system_stopped;
        Primus.Interpreter.written >>> Exec.written;
        Primus.Memory.protected >>> Exec.protected;
        Primus.Track.marked >>> Exec.marked;
        Primus.Interpreter.clock >>> Exec.clocked;
        ( Primus.Linker.Trace.lisp_call >>> fun (name, _) ->
          Machine.Local.update lisp_calls ~f:(List.cons name) );
        ( Primus.Linker.Trace.lisp_call_return >>> fun _ ->
          Machine.Local.update lisp_calls ~f:(function
            | _ :: rest -> rest
            | [] -> []) );
      ]
end
