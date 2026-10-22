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
     e.g., memcpy, see [Primus_unicorn_native], which don't copy it to
     Primus.

   A run ends when the subroutine returns, i.e., when the code reaches
   its return address with the stack pointer of the caller.

   A checkpoint of the machine is saved when Unicorn reaches its address
   for the first time, and a machine that restores it continues from
   there, instead of the first subroutine that it runs, e.g., the entry
   point, see [Primus_unicorn_checkpoint]. *)

open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
module Uc = Bap_unicorn
module Target = Primus_unicorn_target
module Checkpoint = Primus_unicorn_checkpoint
module Native = Primus_unicorn_native
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
}

(* the events of the code, that the observers of the machine see, which
   are hooked, only when they are observed, see [Make.watching] *)
and watching = { pcs : bool; reads : bool; writes : bool }

(* The state of a system, whose machines run in Unicorn, which is of the
   system, see [session_state], as the systems, e.g., the emulators of a
   script, see [Bap_emu], run in the same process, each with its own
   engine. *)
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
      (** the processor time, which the machines have accounted for, see
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
  mutable driven : bool;
      (** the script drives the machines, see [Bap_emu], which pause, when
          [pause] is set *)
  mutable pause : bool;
  mutable saved : (unit, string) result;  (** the result of the last [Save] *)
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
      (** the processor time, at which the thread, that runs, started its time
          slice, see [Make.Threads] *)
}

(* the options of the plugin, which are the defaults of the sessions: the
   seconds that a machine may run, the file of the checkpoint and its
   point, the file of the checkpoint to continue from, and the functions
   of libc that run natively *)
let timeout : float option ref = ref None
let checkpoint : (string * string) option ref = ref None
let restore : string option ref = ref None
let native_stubs : String.Set.t ref = ref (String.Set.of_list Native.names)

let create_session ?(restore = !restore) () =
  {
    active = None;
    recipe = None;
    parked = Id.Table.create ();
    parked_pages = 0;
    dead = Id.Hash_set.create ();
    own_code = Addr.Table.create ();
    stubs = Addr.Table.create ();
    native_stubs = !native_stubs;
    natives = String.Table.create ();
    signatures = String.Table.create ();
    names = Int64.Table.create ();
    symbols = Int64.Table.create ();
    unstubbed = Int64.Hash_set.create ();
    thumb = Addr.Hash_set.create ();
    thumb_symbols = Int64.Hash_set.create ();
    bare_mode = false;
    timeout = !timeout;
    accounted = Stdlib.Sys.time ();
    ticks = 0;
    checkpoint = !checkpoint;
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
    starts = 0;
    stopped_at = None;
    restarted_at = None;
    call_hooks = String.Table.create ();
    exit_code = None;
    engine_hooks = [];
    events = Queue.create ();
    sliced_at = 0.;
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
   e.g., clone, which run in the same engine, and share its memory, one
   at a time, see [Make.Threads]. A thread, that doesn't run, keeps the
   values of its registers in the variables of Primus, see [thread_var],
   so that they keep their taint and their formulas, and the
   checkpoints keep them, and the address, from which it continues. *)
type wait = Ready | Waiting of int64  (** on the futex at the address *)

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
}

type threads = {
  current : int;  (** the TID of the thread, that runs *)
  cleared : int64 option;  (** its [clear] *)
  others : thread list;  (** the threads, that don't run, in their order *)
  last : int;  (** the last TID *)
  depth : int option;
      (** the number of the pending returns, at which the threads switch, which
          is of the run, that created the first thread, see [frames] *)
}

(* the registers of a thread, that Primus doesn't have, e.g., of TLS,
   which the checkpoints keep too *)
let extra_regs (e : engine) =
  (match e.arch with
    | X86 -> [ "FS_BASE"; "GS_BASE"; "MXCSR" ]
    | Arm64 -> [ "TPIDR_EL0"; "FPCR"; "FPSR" ]
    | _ -> [])
  |> List.filter_map ~f:(Uc.reg e.arch)

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
      { current = 1; cleared = None; others = []; last = 1; depth = None })

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
  | Save of string * int64
      (** the checkpoint of the machine, which continues from the address, is
          saved to the file, see [Bap_emu.save] *)

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
type intrinsic = { name : string; inputs : (var * exp) list }

(* the intrinsic of the instruction, which the blocks of its IR call *)
let site_of_blocks blks =
  let defs =
    List.concat_map blks ~f:(fun blk -> Term.enum def_t blk |> Seq.to_list)
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

let create session target ~foreign ~externals =
  let arch, mode =
    match Target.engine target with
    | Some e -> e
    | None ->
        failf "the target %s is not supported" (Theory.Target.to_string target)
  in
  let uc = Uc.create arch mode in
  (* the default CPU of AArch64, Cortex-A72, is ARMv8.0, which has no LSE
     atomics of ARMv8.1, e.g., ldadd and cas, that the programs compiled
     for the later ones, or with outline atomics, run; the maximum one has
     all of them, and must be selected before anything else *)
  (match arch with Arm64 -> Uc.set_cpu_model uc Uc.Cpu.arm64_max | _ -> ());
  (* the addresses of the program are the addresses of Unicorn *)
  Uc.set_tlb_virtual uc;
  (* the 64-bit addresses of MIPS are enabled by the KX, SX, and UX bits *)
  (match arch with
  | Mips when Theory.Target.bits target = 64 ->
      let status = Option.value_exn (Uc.reg Mips "CP0_STATUS") in
      Uc.reg_write uc status Int64.(Uc.reg_read uc status lor 0xE0L)
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
      hooked = Int64.Hash_set.create ();
      stops = -1;
      stepper = None;
      watching = { pcs = false; reads = false; writes = false };
      watchers = [];
      observed = None;
      accesses = Int64.Table.create ();
      foreign = Int64.Hash_set.of_list foreign;
      tracked = String.Hash_set.create ();
      clobbered = [];
      tracer = None;
      seen = -1;
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
    if w.writes then
      add
        (Uc.on_mem e.uc [ `write ] (fun _ addr size value ->
             Queue.enqueue e.session.events (Stored (addr, size, value))));
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

(* the name of the function at the address, which Unicorn calls *)
let function_name e addr =
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

  (* the page, which has a tracked location, stays in Primus, so that
     the code, which accesses it, faults, and is interpreted *)
  let ensure_page e addr =
    let page = page_of addr in
    if Hashtbl.mem e.pages page then Machine.return ()
    else
      let* mapped = Memory.is_mapped (word e addr) in
      let* marked = Track.page_marked (word e addr) in
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
    let* vars = Env.all in
    Seq.to_list vars
    |> List.filter ~f:(Target.Regs.mem e.regs)
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
            if tracked then Hash_set.add e.tracked r
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
  and marked addr = drop addr addr

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
        let* marked = Track.page_marked (word e addr) in
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
          let rec attempt tries =
            match
              let args = List.map call.args ~f:(eval_uc e) in
              let frame = frame_uc e in
              let r = call.fn (uc_memory e) (List.map args ~f:int64_of_word) in
              List.iter r.writes ~f:(fun (addr, data) ->
                  uc_check_write e addr (String.length data));
              (args, frame, r)
            with
            | exception Native.Missing addr when tries > 0 ->
                let* () = ensure_page e addr in
                if Hashtbl.mem e.pages (page_of addr) then attempt (tries - 1)
                else Machine.return None
            | exception (Native.Missing _ | Native.Denied) ->
                Machine.return None
            | args, frame, r ->
                let* () =
                  Machine.Observation.post Primus.Linker.Trace.call_entered
                    ~f:(fun notify ->
                      let* args = Machine.List.map args ~f:Value.of_word in
                      notify (name, args))
                in
                List.iter r.writes ~f:(fun (addr, data) -> uc_write e addr data);
                let result =
                  Option.map call.result ~f:(fun (exp, width) ->
                      let x = Word.of_int64 ~width r.value in
                      ignore (assign_uc e exp x : bool);
                      x)
                in
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

  let call_intrinsic e { name; inputs } =
    let* () = pull e in
    let* () =
      Machine.List.iter inputs ~f:(fun (var, exp) ->
          Interpreter.exp exp >>= Interpreter.set var)
    in
    let* () = Linker.exec (`symbol name) in
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
                List.map (extra_regs e) ~f:(fun id ->
                    (id, Uc.reg_read_bytes e.uc id));
              threads =
                (if threads.last = 1 then None
                 else
                   Some
                     {
                       current = threads.current;
                       cleared = threads.cleared;
                       last = threads.last;
                       others =
                         List.map threads.others
                           ~f:(fun { tid; saved_extra; next; wait; clear } ->
                             {
                               Checkpoint.tid;
                               extra = saved_extra;
                               next;
                               clear;
                               waiting =
                                 (match wait with
                                 | Ready -> None
                                 | Waiting addr -> Some addr);
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
        let now = Stdlib.Sys.time () in
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
  let rec start_uc e pc deadline =
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
        Uc.start e.uc pc
          ?timeout:
            (Option.map deadline ~f:(fun t ->
                 Int.max 1
                   (Float.iround_up_exn ((t -. Stdlib.Sys.time ()) *. 1e6))));
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
        start_uc e pc deadline
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
    let* loaded = observed Primus.Interpreter.loaded in
    let* storing = observed Primus.Interpreter.storing in
    let+ stored = observed Primus.Interpreter.stored in
    watch e { pcs; reads = loading || loaded; writes = storing || stored }

  (* the loads and the stores of the code, that Unicorn ran, which the
     observers see byte by byte, as they see those of Primus *)
  let observe e =
    let events = e.session.events in
    if Queue.is_empty events then Machine.return ()
    else
      let happened = Queue.to_list events in
      Queue.clear events;
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
      push_owned e

  (* the registers, whose values Primus tracks, after the tracked
     values change, e.g., when taint is introduced, see [trace] *)
  let tracking e =
    let* version = Track.version in
    let* () =
      if version = e.seen then Machine.return ()
      else
        let* () = pull_regs e in
        e.seen <- version;
        Hash_set.clear e.tracked;
        let* active = Track.active in
        if not active then Machine.return ()
        else
          let* vars = Env.all in
          Machine.Seq.iter vars ~f:(fun v ->
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
    let lo = Int64.(max 0L (addr - of_int Primus.Lift.max_size)) in
    let n = Int64.to_int_exn Int64.(addr + of_int Primus.Lift.max_size - lo) in
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

  (* The system calls of Linux, that create and run the threads, see
     [threads], which run one at a time, in the engine, and switch, when
     the thread, that runs, waits, exits, or yields, or else, when its
     time slice ends, see [loop]. They switch only in the run, that
     created the first thread, as a stub, that runs a function of the
     program, returns to the thread, that called it. The calls of the
     processes, e.g., clone without CLONE_VM, and the other calls go to
     the intrinsic functions, as before. *)
  module Threads = struct
    (* the registers of the calls: the number, the arguments, the
       result, and the register of TLS, which Primus doesn't have *)
    type abi = {
      number : string;
      args : string list;
      result : string;
      tls : string;
    }

    let abi (e : engine) =
      match e.arch with
      | X86 when e.bytes = 8 ->
          Some
            {
              number = "RAX";
              args = [ "RDI"; "RSI"; "RDX"; "R10"; "R8"; "R9" ];
              result = "RAX";
              tls = "FS_BASE";
            }
      | Arm64 ->
          Some
            {
              number = "R8";
              args = [ "R0"; "R1"; "R2"; "R3"; "R4"; "R5" ];
              result = "R0";
              tls = "TPIDR_EL0";
            }
      | _ -> None

    let extra = extra_regs

    type call =
      | Clone
      | Clone3
      | Futex
      | Set_tid_address
      | Gettid
      | Sched_yield
      | Exit
      | Exit_group

    let call (e : engine) n =
      match (e.arch, n) with
      | X86, 56 | Arm64, 220 -> Some Clone
      | (X86 | Arm64), 435 -> Some Clone3
      | X86, 202 | Arm64, 98 -> Some Futex
      | X86, 218 | Arm64, 96 -> Some Set_tid_address
      | X86, 186 | Arm64, 178 -> Some Gettid
      | X86, 24 | Arm64, 124 -> Some Sched_yield
      | X86, 60 | Arm64, 93 -> Some Exit
      | X86, 231 | Arm64, 94 -> Some Exit_group
      | _ -> None

    let get e name =
      Option.value_map
        (Target.Regs.read_name e.regs name)
        ~default:0L ~f:int64_of_word

    let set e name x =
      ignore (Target.Regs.write_name e.regs name (word e x) : bool)

    (* if the call of the intrinsic function [site] is of the threads,
       by its [number] *)
    let is_call e { name; _ } number =
      (String.equal name "intrinsic:syscall"
      || String.equal name "intrinsic:svc")
      && Option.is_some (abi e)
      && Option.is_some (call e (Int64.to_int_trunc number))

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

    (* the bytes of the word at [addr] in Primus, if they all have the
       [access], as the page, whose locations are marked, e.g., tainted,
       is not in Unicorn, see [ensure_page] *)
    let primus_word e addr access =
      let+ loaded = Memory.load_bytes (word e addr) 4 in
      if
        Array.for_all loaded ~f:(function
          | Some (_, p) -> access p
          | None -> false)
      then
        Some
          (String.of_array
             (Array.map loaded ~f:(fun b -> fst (Option.value_exn b))))
      else None

    (* the futexes and the TIDs are the words of 32 bits *)
    let load32 e addr =
      let* () = ensure_page e addr in
      if Hashtbl.mem e.pages (page_of addr) then
        Machine.return
          (match uc_read e addr 4 with
          | data -> Some (value e data)
          | exception (Native.Missing _ | Native.Denied) -> None)
      else primus_word e addr (fun p -> p.readable) >>| Option.map ~f:(value e)

    let store32 e addr x =
      let* () = ensure_page e addr in
      if Hashtbl.mem e.pages (page_of addr) then
        Machine.return
          (match uc_check_write e addr 4 with
          | () ->
              uc_write e addr (bytes e x 4);
              true
          | exception (Native.Missing _ | Native.Denied) -> false)
      else
        primus_word e addr (fun p -> p.writable) >>= function
        | None -> Machine.return false
        | Some _ ->
            Memory.store_bytes (word e addr) (bytes e x 4) >>| fun () -> true

    (* the thread, that runs, as it continues from [next] *)
    (* the registers, that are set, the aliases too, e.g., EAX *)
    let registers e =
      let* vars = Env.all in
      Seq.to_list vars
      |> List.filter ~f:(Target.Regs.mem e.regs)
      |> Machine.List.filter ~f:Env.is_set

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
        saved_extra =
          List.map (extra e) ~f:(fun id -> (id, Uc.reg_read_bytes e.uc id));
        next;
        wait;
        clear = st.cleared;
      }

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
                if tracked then Hash_set.add e.tracked (Var.name v)
                else Hash_set.remove e.tracked (Var.name v))
      in
      (* the aliases, that are set, are of the thread, if their saved
         values are the bits of their registers, e.g., with their taint,
         and else are read anew, so that the ones of the other thread,
         e.g., tracked, don't stay *)
      let basis = Target.Regs.basis e.regs in
      let+ () =
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
      List.iter thread.saved_extra ~f:(fun (id, data) ->
          Uc.reg_write_bytes e.uc id data);
      e.written <- []

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
          e.session.sliced_at <- Stdlib.Sys.time ();
          let+ () =
            Machine.Local.put threads
              {
                st with
                current = next.tid;
                cleared = next.clear;
                others = List.filteri others ~f:(fun j _ -> j <> i);
              }
          in
          Some next.next

    (* the threads, that wait on the futex at [addr], at most [n], are
       ready, the first first *)
    let wake st addr n =
      let woken = ref 0 in
      let others =
        List.map st.others ~f:(fun t ->
            match t.wait with
            | Waiting a when Int64.equal a addr && !woken < n ->
                incr woken;
                { t with wait = Ready }
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
      let* parked = park e ~next:pc ~wait:Ready st in
      switch e ~parked st >>| function Some pc -> pc | None -> pc

    let flag flags bit = Int64.(flags land bit <> 0L)

    (* the call of the thread, that runs, after which the thread, that
       runs then, continues from the address, or [None], if it isn't a
       call of the threads *)
    let syscall e ~next =
      match abi e with
      | None -> Machine.return None
      | Some abi -> (
          let arg i = get e (List.nth_exn abi.args i) in
          match call e (Int64.to_int_trunc (get e abi.number)) with
          | None -> Machine.return None
          | Some call -> (
              let* st = Machine.Local.get threads in
              let return x =
                set e abi.result x;
                Machine.return (Some next)
              in
              match call with
              | Clone3 -> return (-38L)
              | Gettid -> return (Int64.of_int st.current)
              | Set_tid_address ->
                  let* () =
                    Machine.Local.put threads { st with cleared = Some (arg 0) }
                  in
                  return (Int64.of_int st.current)
              | Exit_group -> exit_process e (arg 0)
              | Sched_yield ->
                  set e abi.result 0L;
                  if ready e st then
                    let* parked = park e ~next ~wait:Ready st in
                    switch e ~parked st
                  else Machine.return (Some next)
              | Clone ->
                  let flags = arg 0 and stack = arg 1 and ptid = arg 2 in
                  let ctid, tls =
                    match e.arch with
                    | X86 -> (arg 3, arg 4)
                    | _ -> (arg 4, arg 3)
                  in
                  (* the processes, that don't share the memory *)
                  if not (flag flags 0x100L) then return (-38L)
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
                    (* the child has the values of the registers of
                       the parent, e.g., their taint, but the result,
                       the stack, and TLS *)
                    let* () =
                      copy e tid ~changed:(fun v x ->
                          if String.equal (Var.name v) abi.result then
                            Value.of_word (word e 0L)
                          else if Var.equal v e.sp && Int64.(stack <> 0L) then
                            Value.of_word (word e stack)
                          else Machine.return x)
                    in
                    let tls_id = Uc.reg e.arch abi.tls in
                    let child =
                      {
                        tid;
                        saved_extra =
                          List.map (extra e) ~f:(fun id ->
                              let data = Uc.reg_read_bytes e.uc id in
                              if
                                flag flags 0x80000L
                                && Option.equal Int.equal (Some id) tls_id
                              then (id, bytes e tls (String.length data))
                              else (id, data));
                        next;
                        wait = Ready;
                        clear =
                          (if flag flags 0x200000L then Some ctid else None);
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
                      | None -> return (-14L)
                      | Some x when Int64.(x <> value) -> return (-11L)
                      | Some _ -> (
                          if not (switchable e st) then
                            fail "the thread %d waits in a run of a stub"
                              st.current
                          else
                            (* it returns 0, when it is woken *)
                            let () = set e abi.result 0L in
                            let* parked =
                              park e ~next ~wait:(Waiting addr) st
                            in
                            switch e ~parked st >>= function
                            | Some pc -> Machine.return (Some pc)
                            | None when Int64.(arg 3 <> 0L) -> return (-110L)
                            | None ->
                                fail "the threads wait, the last one on %Lx"
                                  addr))
                  | 1 | 10 ->
                      let st, woken = wake st addr (Int64.to_int_trunc value) in
                      let* () = Machine.Local.put threads st in
                      return (Int64.of_int woken)
                  | _ -> return (-38L))
              | Exit -> (
                  let* st =
                    match st.cleared with
                    | None -> Machine.return st
                    | Some addr ->
                        let+ _ = store32 e addr 0L in
                        fst (wake st addr 1)
                  in
                  if List.is_empty st.others then exit_process e (arg 0)
                  else
                    switch e st >>= function
                    | Some pc -> Machine.return (Some pc)
                    | None ->
                        fail "the threads wait, after the thread %d exited"
                          st.current)))
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
      else if memory then Track.has_marks
      else Machine.return false

  (* Primus interprets the instructions from [pc], see [trace], while
     they continue, see [continues], and returns the address of the next
     one, which on ARM stays in the Thumb state, unless the jump sets the
     lower bit *)
  let interpret e pc =
    let* () = pull e in
    (* the call of the threads runs in Unicorn, see [Threads] *)
    let threads_call site =
      match Threads.abi e with
      | None -> Machine.return false
      | Some { number; _ } ->
          let+ n = Env.get (Var.create number (Type.imm (e.bytes * 8))) in
          Threads.is_call e site (int64_of_word (Primus.Value.to_word n))
    in
    let stopped = ref false in
    let rec run pc n =
      lift ~thumb:(in_thumb e pc) e (code_addr e pc) >>= function
      | None -> fail "can't interpret the instruction at %Lx" pc
      | Some (size, blks) ->
          let next = Int64.(pc + of_int size) in
          let* pc =
            match site_of_blocks blks with
            | Some site -> (
                threads_call site >>= function
                | true ->
                    stopped := true;
                    Machine.return pc
                | false -> call_intrinsic e site >>| fun () -> next)
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
                | _ ->
                    let+ dst = Interpreter.step ~next blks in
                    int64_of_word (Primus.Value.to_word dst))
          in
          let* more =
            if n > 1 && not !stopped then continues e pc
            else Machine.return false
          in
          if more then run pc (n - 1) else Machine.return pc
    in
    let* pc = run pc 4096 in
    let+ () = push_owned e in
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
      (* the thread, that paused, didn't run, so its time slice starts
         anew, and it runs the instruction, at which it paused *)
      serve pc
      >>= fun pc ->
      s.sliced_at <- Stdlib.Sys.time ();
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
          let now = Stdlib.Sys.time () in
          let ends = s.sliced_at +. Threads.slice in
          if sliced && Float.(now >= ends) then Threads.preempt e pc >>= loop
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
            let error = start_uc e pc deadline in
            let* () = account () in
            let* () = observe e in
            let pc = current_pc e in
            (match e.reason with
            | Some (Fault _ | Unknown _)
              when Option.equal Int64.equal s.skipped_at (Some (code_addr e pc))
              ->
                s.resumed_at <- s.skipped_at
            | _ -> ());
            match (e.reason, error) with
            | None, None when sliced -> Threads.preempt e pc >>= loop
            | None, None when Option.is_some remaining -> loop pc
            | Some Returned, _ | None, None -> pull e
            | Some (Foreign addr), _ -> (
                match
                  Option.bind (function_name e addr) ~f:(call_returns e)
                with
                | Some pc -> loop pc
                | None -> (
                    native e addr >>= function
                    | Some pc -> loop pc
                    | None -> call_foreign e addr >>= loop))
            | Some (Pause | Interrupted), _ -> loop pc
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
                fault e access addr >>= function
                | `Continue -> loop pc
                | `Interpret -> interpret e pc >>= loop)
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
                pull e >>= fun () -> fail "an invalid instruction at %Lx" pc
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
    List.iter cp.extra ~f:(fun (id, data) -> Uc.reg_write_bytes e.uc id data);
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
          | Some { current; cleared; others; last } ->
              Machine.Local.put threads
                {
                  current;
                  cleared;
                  last;
                  depth = Some (List.length pending + 1);
                  others =
                    List.map others
                      ~f:(fun { tid; extra; next; waiting; clear } ->
                        {
                          tid;
                          saved_extra = extra;
                          next;
                          clear;
                          wait =
                            (match waiting with
                            | None -> Ready
                            | Some addr -> Waiting addr);
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

  let restore data =
    Machine.Local.put elapsed
      (Option.value (Float.of_string_opt data) ~default:0.)
end

let () =
  Primus.Checkpoint.register ~package:"bap" "unicorn-elapsed" (module Elapsed)

(* links the program, as load-binary does, except that its subroutines
   run in Unicorn, and keeps the linked code to tell the addresses of the
   subroutines that other components replace *)
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
      String.is_empty digest
      ||
      match program with
      | None -> true
      | Some file -> (
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
    match create s target ~foreign ~externals with
    | exception Unsupported msg -> Machine.raise (Unicorn_failure msg)
    | e ->
        s.active <- Some e;
        Hashtbl.clear s.parked;
        s.parked_pages <- 0;
        Memory.set_backing
          (Some (backing s (Theory.Var.name (Theory.Target.data target))))

  (* the session, that the script created for the system, see
     [Bap_emu.create], or a new one *)
  let start_session =
    let* proj = Machine.get () in
    let s =
      match
        Option.bind
          (Project.get proj session_tag)
          ~f:(Hashtbl.find_and_remove sessions)
      with
      | Some s -> s
      | None -> create_session ()
    in
    s.bare_mode <- not (Project.disassembled proj);
    index_thumb_symbols s (Project.specification proj);
    let* () = Machine.Global.put session_state s in
    link_program s

  let init () =
    let module Exec = Make (Machine) in
    Machine.sequence
      [
        start_session;
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
