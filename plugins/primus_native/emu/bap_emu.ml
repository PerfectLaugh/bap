open Core
open Bap_knowledge
open Bap.Std
open Bap_primus.Std
module X = Bap_primus_native_plugin.Primus_native_executor
module Native = Bap_primus_native_plugin.Primus_native_libc
module Target = Bap_primus_native_plugin.Primus_native_target
module Engine = Bap_engine
module Io = Primus_lisp_library_plugin.Primus_lisp_io
include Bap_main.Loggers ()

type status = Paused | Running | Exited of int option | Failed of string
type action = Default | Return of int64
type memory_operation = Read | Write | Fetch

type failure = {
  thread : int;
  pc : int64;
  addr : int64;
  operation : memory_operation;
}

type event = { kind : string; detail : string }
type checkpoint_models = X.model_registry
type write_profile = { dispatches : int; callbacks : int; seconds : float }

(* the system, which runs in the fiber of the script, either paused,
   with the address, from which it continues, or finished *)
type state =
  | Suspended of
      int64 * Primus.Machine.id * (X.request, state) Effect.Deep.continuation
  | Finished of
      ( Primus.exit_status * project * Knowledge.state,
        Knowledge.conflict )
      result
  | Crashed of exn
  | Ended of Primus.exit_status * (X.request, state) Effect.Deep.continuation
  | Running  (** the program runs, e.g., in a hook *)

(* the machine, which is of the system of the emulator, as the systems
   number their machines alike *)
type snapshot = { owner : X.session; id : Primus.Machine.id }

(* the state of the shell, see [shell]: the breakpoints, with the
   functions, that remove them, and the snapshots, the last first *)
type shell_state = {
  breaks : (unit -> unit) Int64.Table.t;
  mutable snaps : snapshot list;
}

(* the emulator, whose system has its own session, i.e., its own engine
   and the state of the executor, so that the emulators run side by side *)
type t = {
  session : X.session;
  mutable state : state;
  mutable call : string option;
  target : Bap_core_theory.Theory.Target.t;
  project : project;
  mutable hooked : Knowledge.state option;
      (** the knowledge, in which [bir] lifts the instructions in the hooks,
          outside of the machine, which runs *)
  lifted : (int64 * string * bool, (int * blk term list) option) Hashtbl.t;
      (** the instructions, that [bir] lifted in the hooks, of the program, see
          [lifts] *)
  paused_lifts :
    (int64 * string * bool, (int * blk term list) option) Hashtbl.t;
      (** the instructions, that [bir] lifted in the machine, as the machine is
          not free to call *)
  hooked_calls : Int64.Hash_set.t;
      (** the addresses, whose calls the script hooks, see [on_call] *)
  services : int String.Table.t;
      (** the active hooks of each import, that the script services *)
  insns : Int64.Hash_set.t Lazy.t;
      (** the addresses of the instructions of the program, that the
          disassembler computed, if any, see [it_blocks_of] *)
  thumb_insns : string Int64.Table.t;
      (** the instructions of Thumb, that [bir] lifted, by their addresses, with
          their first halfwords, which are the instructions, while the halfwords
          are the same, see [it_blocks_of] *)
  deferred : (t -> unit) Queue.t;
      (** the actions, that the hooks deferred to the next pause, see [defer] *)
  saves : string Queue.t;
      (** checkpoints, that wait until all deferred model mutations finish *)
  mutable serving : bool;
  mutable stopped : bool;
      (** if a hook stopped the program, see [stop], so that it stays paused
          after the deferred actions *)
  mutable scopes : (unit -> unit) list ref list;
      (** the functions, that remove the hooks, that the scopes added, the
          innermost scope first, see [scoped] *)
  mutable write_dispatches : int;
  mutable write_callbacks : int;
  mutable write_seconds : float;
  mutable instructions : int64;
  lift_cleanup : X.operation;
  block_reclamation : X.operation;
  heap_compaction : X.operation;
  mutable snapshots : snapshot list;  (** the managed snapshots, oldest first *)
  mutable snapshot_limit : int option;
  mutable traces :
    (Engine.Trace.t Weak.t * (int * int64 array) list Int64.Table.t Weak.t) list;
  shell : shell_state;
}

type stack_stats = {
  lower : int64;
  upper : int64;
  lowest_sp : int64;
  max_usage : int64;
}

type execution_stats = {
  instructions : int64;
  lifted_blocks : int;
  active_threads : int;
  hook_dispatches : int;
  rss : int option;
  last_pc : int64;
  stack : stack_stats option;
}

type operation_stats = { count : int; seconds : float }

type maintenance_stats = {
  lru_reconstruction : operation_stats;
  entry_eviction : operation_stats;
  cache_load : operation_stats;
  cache_merge : operation_stats;
  cache_write : operation_stats;
  lift_cleanup : operation_stats;
  block_reclamation : operation_stats;
  heap_compaction : operation_stats;
  cache_entries_written : int;
  cache_bytes_written : int;
}

type stats_subscription = {
  interval : float;
  callback : execution_stats -> unit;
  mutable next : float;
  mutable active : bool;
  mutable stop : unit -> unit;
}

type write_subscription = {
  first : int64 option;
  last : int64 option;
  primus : bool;
  deferred : bool;
  callback : t -> int64 -> int -> int64 -> unit;
}

let engine t =
  match t.session.active with
  | Some e -> e
  | None -> invalid_arg "Bap_emu: the engine is not running"

let fiber f =
  Effect.Deep.match_with f ()
    {
      retc = (fun result -> Finished result);
      exnc = (fun exn -> Crashed exn);
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | X.Paused (pc, id) ->
              Some
                (fun (k : (a, state) Effect.Deep.continuation) ->
                  Suspended (pc, id, k))
          | X.Ended status ->
              Some
                (fun (k : (a, state) Effect.Deep.continuation) ->
                  Ended (status, k))
          | _ -> None);
    }

(* the knowledge of the finished system is of the emulator, see
   [knowledge], e.g., of the instructions, that it lifted, see
   [Primus.Lift], and doesn't replace the toplevel one, as each emulator
   has its own *)
let finish t state =
  t.state <- state;
  match state with
  | Suspended _ | Ended _ | Running -> ()
  | Finished _ | Crashed _ -> t.session.driven <- false

let status t =
  match t.state with
  | Suspended _ -> Paused
  | Running -> Running
  | Ended ((Primus.Normal | Exn Primus.Interpreter.Halt), _) ->
      Exited t.session.exit_code
  | Ended (Exn exn, _) -> Failed (Primus.Exn.to_string exn)
  | Finished (Ok ((Primus.Normal | Exn Primus.Interpreter.Halt), _, _)) ->
      Exited t.session.exit_code
  | Finished (Ok (Exn exn, _, _)) -> Failed (Primus.Exn.to_string exn)
  | Finished (Error conflict) ->
      Failed (Format.asprintf "%a" Knowledge.Conflict.pp conflict)
  | Crashed exn -> Failed (Exn.to_string exn)

let failure t =
  Option.map t.session.last_fault ~f:(fun (fault : X.fault) ->
      let operation =
        match fault.access with
        | Engine.Read | Engine.Read_after | Engine.Read_unmapped
        | Engine.Read_prot ->
            Read
        | Engine.Write | Engine.Write_unmapped | Engine.Write_prot -> Write
        | Engine.Fetch | Engine.Fetch_unmapped | Engine.Fetch_prot -> Fetch
      in
      { thread = fault.tid; pc = fault.pc; addr = fault.addr; operation })

let record_event t kind detail = X.record_event t.session kind detail
let paused t = match t.state with Suspended _ -> true | _ -> false

(* the failure of [fn], whose program is not paused, which tells, why:
   it runs, e.g., in a hook, where the machine serves no request, or
   it ended, with its code, or its failure *)
let not_paused ?fn t =
  let fn = Option.value_map fn ~default:"Bap_emu" ~f:(( ^ ) "Bap_emu.") in
  match status t with
  | Running ->
      invalid_argf
        "%s: the program is not paused, as it runs, e.g., in a hook, where the \
         machine serves no request: stop it there, see Bap_emu.stop, or defer \
         the action to the pause, see Bap_emu.defer"
        fn ()
  | Exited (Some code) ->
      invalid_argf
        "%s: the program is not paused, as it exited with the code %d" fn code
        ()
  | Exited None ->
      invalid_argf "%s: the program is not paused, as it exited" fn ()
  | Failed msg ->
      invalid_argf "%s: the program is not paused, as it failed: %s" fn msg ()
  | Paused -> invalid_argf "%s: the program is paused" fn ()

(* continues the paused system with the request, and serves the
   actions, that the hooks deferred to the pause, see [defer] *)
let rec resume t request =
  match t.state with
  | Suspended (_, _, k) | Ended (_, k) ->
      (* the hooks see, that the program runs, and its continuation is
         not resumed again *)
      t.state <- Running;
      (match request with
      | X.Continue _ | X.Call _ | X.Interpret -> t.stopped <- false
      | _ -> ());
      finish t (Effect.Deep.continue k request);
      served t
  | _ -> not_paused t

(* the deferred actions run at the pause, that they asked for, which
   is before the instruction, that the hook saw, after which the program
   continues, unless a hook stopped it too, or it ended *)
and served t =
  if
    (not t.serving)
    && ((not (Queue.is_empty t.deferred)) || not (Queue.is_empty t.saves))
  then begin
    let stopped = t.stopped in
    t.serving <- true;
    Exn.protect
      ~f:(fun () ->
        while not (Queue.is_empty t.deferred) do
          (Queue.dequeue_exn t.deferred) t
        done;
        while not (Queue.is_empty t.saves) do
          let file = Queue.dequeue_exn t.saves in
          (match t.state with
          | Suspended (pc, _, _) -> resume t (X.Save (file, pc))
          | _ -> not_paused ~fn:"save" t);
          Option.iter t.session.lifter ~f:(fun l -> l.save ());
          match t.session.saved with Ok () -> () | Error msg -> failwith msg
        done)
      ~finally:(fun () -> t.serving <- false);
    match t.state with
    | Suspended (pc, _, _) when not (stopped || t.stopped) ->
        resume t (X.Continue pc)
    | _ -> ()
  end

(* pauses the program before the next instruction, from a hook *)
let pause t =
  let e = engine t in
  t.session.pause <- true;
  e.reason <- Some X.Pause;
  Engine.stop e.engine

let stop t =
  t.stopped <- true;
  if not (paused t) then pause t

(* the action runs, when the program is paused: now, or, in a hook,
   where the machine runs the program, and serves no request, at the
   pause, that the hook asks for, see [served] *)
let defer t f =
  match t.state with
  | Suspended _ -> f t
  | Running ->
      Queue.enqueue t.deferred f;
      pause t
  | _ -> invalid_arg "Bap_emu.defer: the program ended"

(* the program runs from the entry, and, when it ends, the script may
   restore a snapshot, after which the machine, that ended, is killed,
   and the snapshot continues, which ends here too *)
let start init (entry : Primus.Linker.name) =
  let module Machine = Primus.Analysis in
  let module Linker = Primus.Linker.Make (Machine) in
  let open Machine.Syntax in
  Machine.List.iter init ~f:(fun component ->
      let module Component = (val component : Primus.Machine.Component) in
      let module Component = Component (Machine) in
      Component.init ())
  >>= fun () ->
  Machine.catch
    (Linker.exec entry >>| fun () -> Primus.Normal)
    (fun exn -> Machine.return (Primus.Exn exn))
  >>= fun status ->
  let rec ended () =
    match Effect.perform (X.Ended status) with
    | X.Restore snapshot ->
        Machine.current () >>= fun id ->
        Machine.kill id >>= fun () -> Machine.switch snapshot
    | X.Run component ->
        let module Component = (val component : Primus.Machine.Component) in
        let module Component = Component (Machine) in
        Component.init () >>= ended
    | X.Continue _ | X.Map _ | X.Snapshot | X.Store _ | X.Save _ | X.Interpret
    | X.Set_pc _ | X.Spawn _ | X.Resume_thread _ | X.Call _ | X.Regions
    | X.Dump _ | X.Values _ | X.Stored_count | X.Origins _ | X.Drop _ ->
        Machine.return ()
  in
  ended ()

(* the instructions, that the hooks lift, are of the file and the
   target, and not of the emulator, as their bytes are in the key, so
   the emulators of the same program share them, e.g., the ones of a
   script, which creates one for each case, see [hooked] *)
let shared_lifts = Hashtbl.Poly.create ()

let lifts proj =
  match Project.get proj filename with
  | None -> Hashtbl.Poly.create ()
  | Some file ->
      Hashtbl.find_or_add shared_lifts
        (file, Bap_core_theory.Theory.Target.to_string (Project.target proj))
        ~default:Hashtbl.Poly.create

(* the components of [init], and the redirections run
   in the machine, after the components of the system, before the
   program starts, and the program continues from the checkpoint
   [restore], with its names, which the executor loads, when it starts.
   The system gets the session of the emulator with its project, see
   [X.with_session] *)
let create ?system ?(components = []) ?(init = []) ?(redirects = [])
    ?(args = []) ?(envp = []) ?entry ?restore ?models ?engine proj =
  (* the engine of the system, if it is of one, or else of BAP_EMU_ENGINE,
     e.g., of the testsuite, by default the lifted one, see bap_emu.mli *)
  let engine : X.kind =
    match (engine, system) with
    | Some engine, _ -> engine
    | None, Some system
      when String.is_substring system ~substring:"lifted-executor" ->
        `Lifted
    | None, Some system
      when String.is_substring system ~substring:"unicorn-executor" ->
        `Unicorn
    | None, None
      when Option.equal String.equal
             (Sys.getenv "BAP_EMU_ENGINE")
             (Some "unicorn") ->
        `Unicorn
    | None, _ -> `Lifted
  in
  let system =
    Option.value system
      ~default:
        (match engine with
        | `Unicorn -> "bap:unicorn-executor"
        | `Lifted -> "bap:lifted-executor")
  in
  let init =
    init @ if List.is_empty redirects then [] else [ Io.redirect redirects ]
  in
  (* the entry point of the program, as the run pass finds it *)
  let entry =
    match entry with
    | Some name -> `symbol name
    | None -> (
        match
          Term.enum sub_t (Project.program proj)
          |> Seq.find ~f:(fun sub -> Term.has_attr sub Sub.entry_point)
        with
        | Some sub -> `tid (Term.tid sub)
        | None -> `symbol "_start")
  in
  let system =
    match Primus.System.Repository.find (Knowledge.Name.read system) with
    | Some sys -> sys
    | None -> invalid_argf "Bap_emu: unknown system %s" system ()
  in
  let system =
    List.fold components ~init:system ~f:(fun sys comp ->
        let name = Knowledge.Name.read comp in
        Primus.System.add_component sys
          ~package:(Knowledge.Name.package name)
          (Knowledge.Name.unqualified name))
  in
  let program = Option.value (Project.get proj filename) ~default:"a.out" in
  let session =
    X.create_session
      ?restore:(Option.map restore ~f:Option.return)
      ?models ~engine ()
  in
  session.driven <- true;
  session.pause <- true;
  let t =
    {
      session;
      state = Crashed (Failure "not started");
      call = None;
      target = Project.target proj;
      project = proj;
      hooked = None;
      lifted = lifts proj;
      paused_lifts = Hashtbl.Poly.create ();
      hooked_calls = Int64.Hash_set.create ();
      services = String.Table.create ();
      insns =
        lazy
          (let insns = Int64.Hash_set.create () in
           let add a =
             Hash_set.add insns (Bitvec.to_int64 (Word.to_bitvec a))
           in
           let term t = Option.iter (Term.get_attr t address) ~f:add in
           Term.enum sub_t (Project.program proj)
           |> Seq.iter ~f:(fun sub ->
               Term.enum blk_t sub
               |> Seq.iter ~f:(fun blk ->
                   term blk;
                   Seq.iter (Term.enum def_t blk) ~f:term;
                   Seq.iter (Term.enum jmp_t blk) ~f:term));
           Seq.iter
             (Disasm.insns (Project.disasm proj))
             ~f:(fun (mem, _) -> add (Memory.min_addr mem));
           insns);
      thumb_insns = Int64.Table.create ();
      deferred = Queue.create ();
      saves = Queue.create ();
      serving = false;
      stopped = false;
      scopes = [];
      write_dispatches = 0;
      write_callbacks = 0;
      write_seconds = 0.;
      instructions = 0L;
      lift_cleanup = X.operation ();
      block_reclamation = X.operation ();
      heap_compaction = X.operation ();
      snapshots = [];
      snapshot_limit = None;
      traces = [];
      shell = { breaks = Int64.Table.create (); snaps = [] };
    }
  in
  finish t
    (fiber (fun () ->
         Primus.System.run system
           (X.with_session proj session)
           (Toplevel.current ())
           ~args:(Array.of_list (program :: args))
           ~envp:(Array.of_list envp) ~start:(start init entry)));
  t

let pc t =
  match t.state with
  | Suspended (pc, _, _) -> pc
  | Running ->
      (* in a hook, the instruction, that runs, with the lower bit set
         in the Thumb state of ARM, as Unicorn has it *)
      let e = engine t in
      let pc = Engine.current e.engine ~pc:e.pc in
      if
        Poly.equal e.arch Engine.Arm
        && Int64.(
             Engine.reg_read e.engine
               (Option.value_exn (Bap_engine_unicorn.reg Engine.Arm "CPSR"))
             land 0x20L
             <> 0L)
      then Int64.(pc lor 1L)
      else pc
  | _ -> not_paused t

(* the machine continues from the address, also after the other
   requests, e.g., of the snapshots, which the machine serves at its
   address *)
let set_pc t addr =
  match t.state with
  | Suspended _ -> resume t (X.Set_pc addr)
  | _ -> not_paused t

let machine t =
  match t.state with Suspended (_, id, _) -> id | _ -> not_paused t

let same_snapshot id (snap : snapshot) =
  Monads.Std.Monad.State.Multi.Id.equal id snap.id

let unmanage_snapshot t id =
  t.snapshots <- List.filter t.snapshots ~f:(fun s -> not (same_snapshot id s));
  t.shell.snaps <-
    List.filter t.shell.snaps ~f:(fun s -> not (same_snapshot id s))

(* the machine, that takes the snapshot, forks, and stays paused, as the
   snapshot, and its fork continues *)
let rec snapshot t =
  let id = machine t in
  resume t X.Snapshot;
  Hash_set.add t.session.snapshots id;
  let snap = { owner = t.session; id } in
  t.snapshots <- t.snapshots @ [ snap ];
  trim_snapshots t;
  snap

and trim_snapshots t =
  match (t.snapshot_limit, t.snapshots) with
  | Some limit, oldest :: _ when List.length t.snapshots > limit ->
      drop_snapshot t oldest;
      trim_snapshots t
  | _ -> ()

and restore t { owner; id } =
  if not (phys_equal owner t.session) then
    invalid_arg "Bap_emu.restore: the snapshot is of another emulator";
  if Hash_set.mem t.session.dead id then
    invalid_arg "Bap_emu.restore: the snapshot was dropped";
  t.session.exit_code <- None;
  resume t (X.Restore id)

and drop_snapshot t { owner; id } =
  if not (phys_equal owner t.session) then
    invalid_arg "Bap_emu.drop_snapshot: the snapshot is of another emulator";
  if not (paused t) then not_paused ~fn:"drop_snapshot" t;
  unmanage_snapshot t id;
  if not (Hash_set.mem t.session.dead id) then (
    resume t (X.Drop id);
    Hash_set.remove t.session.snapshots id)

and set_snapshot_limit t limit =
  Option.iter limit ~f:(fun capacity ->
      if capacity < 0 then
        invalid_arg "Bap_emu.set_snapshot_limit: the limit must be nonnegative");
  if not (paused t) then not_paused ~fn:"set_snapshot_limit" t;
  t.snapshot_limit <- limit;
  trim_snapshots t

module type Completion = X.Completion

let complete = X.complete
let save_lifts t = Option.iter t.session.lifter ~f:(fun l -> l.save ())

(* the lifted instructions, that the lifter keeps for the engines and
   the cache, and that the hooks lifted, are dropped, after they are
   saved, so that a long run gives their memory back *)
let forget_lifts (t : t) =
  X.measure t.lift_cleanup (fun () ->
      Option.iter t.session.lifter ~f:(fun l -> l.forget ());
      Hashtbl.clear t.lifted;
      Hashtbl.clear t.paused_lifts;
      Hashtbl.clear t.thumb_insns)

let set_lift_cache_limit t limit =
  Option.iter limit ~f:(fun capacity ->
      if capacity < 0 then
        invalid_arg "Bap_emu: the lift-cache limit must be nonnegative");
  Option.iter t.session.lifter ~f:(fun l -> l.set_limit limit)

type footprint = { heap : int; top_heap : int; rss : int option }

(* the resident size of the process, which Linux tells *)
let rss () =
  match In_channel.read_lines "/proc/self/status" with
  | lines ->
      List.find_map lines ~f:(fun line ->
          match String.chop_prefix line ~prefix:"VmRSS:" with
          | Some rest -> (
              match String.split (String.strip rest) ~on:' ' with
              | kb :: _ ->
                  Option.map (Int.of_string_opt kb) ~f:(fun kb -> kb * 1024)
              | [] -> None)
          | None -> None)
  | exception Sys_error _ -> None

let footprint () =
  let s = Gc.quick_stat () in
  let word = Stdlib.Sys.word_size / 8 in
  {
    heap = s.heap_words * word;
    top_heap = s.top_heap_words * word;
    rss = rss ();
  }

type deadline = int64

let start_deadline ?(code = 124) seconds =
  if Float.(seconds < 0.) || not (Float.is_finite seconds) then
    invalid_arg "Bap_emu.start_deadline: invalid seconds";
  Bap_emu_process.start_deadline seconds code

let cancel_deadline = Bap_emu_process.cancel_deadline

type component_footprint = {
  lifter_entries : int;
  lifter_blocks : int;
  knowledge_objects : int;
  lift_history : int;
  engine_entries : int;
  engine_blocks : int;
  jit_blocks : int;
  hook_entries : int;
  stored_bytes : int;
  sparse_pages : int;
  snapshots : int;
  snapshot_bytes : int;
  snapshot_pages : int;
  parked_pages : int;
  trace_records : int;
  trace_accesses : int;
  decoded_blocks : int;
  script_models : int;
}

let components t =
  if not (paused t) then not_paused ~fn:"components" t;
  resume t X.Stored_count;
  let lifter_entries, lifter_blocks, knowledge_objects, lift_history =
    Option.value_map t.session.lifter ~default:(0, 0, 0, 0) ~f:(fun l ->
        let entries, blocks, knowledge_objects = l.inventory () in
        ( entries,
          blocks,
          knowledge_objects,
          List.length (l.ran ()) + Hashtbl.length t.session.ran_before ))
  in
  let engine_entries, engine_blocks, jit_blocks =
    Engine.inventory (engine t).engine
  in
  let traces =
    List.filter_map t.traces ~f:(fun ((trace_slot, blocks_slot) as slots) ->
        match (Weak.get trace_slot 0, Weak.get blocks_slot 0) with
        | None, None -> None
        | trace, blocks -> Some (slots, trace, blocks))
  in
  t.traces <- List.map traces ~f:(fun (slots, _, _) -> slots);
  let trace_records, trace_accesses, decoded_blocks =
    List.fold traces ~init:(0, 0, 0)
      ~f:(fun (records, accesses, decoded) (_, trace, blocks) ->
        let records, accesses =
          Option.value_map trace ~default:(records, accesses) ~f:(fun trace ->
              ( records + Engine.Trace.retained trace,
                accesses + Engine.Trace.retained_accesses trace ))
        in
        let decoded =
          Option.value_map blocks ~default:decoded ~f:(fun blocks ->
              decoded
              + Hashtbl.fold blocks ~init:0 ~f:(fun ~key:_ ~data:blocks count ->
                  count + List.length blocks))
        in
        (records, accesses, decoded))
  in
  {
    lifter_entries;
    lifter_blocks;
    knowledge_objects;
    lift_history;
    engine_entries;
    engine_blocks;
    jit_blocks;
    hook_entries = Hashtbl.length t.lifted + Hashtbl.length t.paused_lifts;
    stored_bytes = t.session.stored_bytes;
    sparse_pages = t.session.sparse_pages;
    snapshots = Hash_set.length t.session.snapshots;
    snapshot_bytes = t.session.snapshot_bytes;
    snapshot_pages = t.session.snapshot_pages;
    parked_pages = t.session.parked_pages;
    trace_records;
    trace_accesses;
    decoded_blocks;
    script_models = Hashtbl.length t.session.models;
  }

(* the checkpoint of the paused program, or, from a hook, of the
   program, as it pauses before the instruction, that the hook sees, see
   [defer] *)
let rec save t file =
  match t.state with
  | Suspended _ when t.serving -> Queue.enqueue t.saves file
  | Suspended _ -> (
      resume t (X.Save (file, pc t));
      save_lifts t;
      match t.session.saved with Ok () -> () | Error msg -> failwith msg)
  | Running -> defer t (fun t -> save t file)
  | Ended (Exn Primus.Interpreter.Halt, _) -> not_paused ~fn:"save" t
  | Ended (Exn _, _) -> save_failed t file
  | _ -> not_paused ~fn:"save" t

(* the checkpoint of the program, that failed, e.g., at the instruction,
   that faulted, from which it continues, as the runs, that the failure
   unwound, are still in the machine, see [X.Make.run] *)
and save_failed t file =
  let saved = ref (Error "the program failed outside of a run") in
  resume t
    (X.Run
       (module functor
                 (Machine : Primus.Machine.S)
                 ->
                 struct
                   module Exec = X.Make (Machine)
                   open Machine.Syntax

                   let init () =
                     Exec.engine () >>= fun e ->
                     Exec.save e (Exec.current_pc e) file >>| fun r ->
                     saved := r
                 end));
  save_lifts t;
  match !saved with Ok () -> () | Error msg -> failwith msg

module Checkpoint = struct
  module C = Bap_primus_native_plugin.Primus_native_checkpoint

  type registry = checkpoint_models

  let create = X.create_model_registry

  let register ?package ?version ?required registry name ~save ~restore =
    X.register_model registry ?package ?version ?required name ~save ~restore

  let register_ref ?package ?version ?required registry name binable state =
    register ?package ?version ?required registry name
      ~save:(fun () -> Some (Binable.to_string binable !state))
      ~restore:(fun data -> state := Binable.of_string binable data)

  let register_table ?package ?version ?required registry name binable table =
    register ?package ?version ?required registry name
      ~save:(fun () ->
        Some (Binable.to_string binable (Hashtbl.to_alist table)))
      ~restore:(fun data ->
        let values = Binable.of_string binable data in
        let restored = Hashtbl.copy table in
        Hashtbl.clear restored;
        List.iter values ~f:(fun (key, data) ->
            ignore (Hashtbl.add restored key data));
        Hashtbl.clear table;
        Hashtbl.iteri restored ~f:(fun ~key ~data ->
            ignore (Hashtbl.add table key data)))

  type thread = { tid : int; pc : int64; waiting : int64 list option }

  type info = {
    target : string;
    digest : string;
    pc : int64;
    thread : int;
    threads : thread list;
    frames : (string option * string option) list;
    symbols : (string * int64) list;
    components : string list;
    quantum_remaining : float;
  }

  let info file =
    match C.load file with
    | Error msg -> failwith msg
    | Ok (c : C.t) ->
        let current, others =
          match c.threads with
          | None -> (1, [])
          | Some t ->
              ( t.current,
                List.map t.others ~f:(fun (o : C.thread) ->
                    { tid = o.tid; pc = o.next; waiting = o.waiting }) )
        in
        {
          target = c.target;
          digest = c.digest;
          pc = c.pc;
          thread = current;
          threads =
            { tid = current; pc = c.pc; waiting = None }
            :: List.sort others ~compare:(fun x y -> Int.compare x.tid y.tid);
          frames =
            List.map c.frames ~f:(fun (f : C.frame) -> (f.callee, f.caller));
          symbols = c.symbols;
          components = List.map c.extensions ~f:fst;
          quantum_remaining = c.quantum_remaining;
        }

  let journal file =
    match C.load file with
    | Error msg -> failwith msg
    | Ok (c : C.t) ->
        List.map c.thread_journal ~f:(fun (event : C.journal_event) ->
            { kind = event.kind; detail = event.detail })

  type model_state = { name : string; version : int; required : bool }

  let models file =
    match C.load file with
    | Error msg -> failwith msg
    | Ok (c : C.t) ->
        Option.map c.model_states ~f:(fun models ->
            List.map models ~f:(fun (m : C.model_state) ->
                { name = m.name; version = m.version; required = m.required }))

  let is_of info proj =
    match Project.get proj filename with
    | None -> false
    | Some file -> (
        try String.equal (C.digest file) info.digest with Sys_error _ -> false)

  (* the addresses of the instructions, that ran, as [insns] tells them,
     with the lower bit set in the Thumb state of ARM *)
  let insns file =
    match C.load file with
    | Error msg -> failwith msg
    | Ok (c : C.t) -> (
        match
          List.Assoc.find c.extensions ~equal:String.equal X.ran_extension
        with
        | None -> []
        | Some data -> (
            match X.ran_of_string data with
            | exception _ ->
                failwithf "Bap_emu.Checkpoint.insns: %s has broken instructions"
                  file ()
            | ran ->
                List.map ran ~f:(fun (pc, thumb, _) ->
                    if thumb then Int64.(pc lor 1L) else pc)
                |> List.dedup_and_sort ~compare:Int64.compare))

  type context = {
    thread : thread;
    frames : (string option * string option) list;
    models : model_state list option;
    failure : failure option;
    events : event list;
  }

  let context file =
    let info = info file in
    let fault, events =
      match C.load file with
      | Error msg -> failwith msg
      | Ok (c : C.t) -> (
          match
            List.Assoc.find c.extensions ~equal:String.equal X.context_extension
          with
          | None -> (None, [])
          | Some data ->
              let context = X.context_of_string data in
              let failure =
                Option.map context.fault ~f:(fun (fault : X.fault_record) ->
                    let operation =
                      match fault.operation with
                      | "read" -> Read
                      | "write" -> Write
                      | "fetch" -> Fetch
                      | _ -> Read
                    in
                    {
                      thread = fault.tid;
                      pc = fault.pc;
                      addr = fault.addr;
                      operation;
                    })
              in
              ( failure,
                List.map context.events ~f:(fun event ->
                    { kind = event.kind; detail = event.detail }) ))
    in
    {
      thread = List.hd_exn info.threads;
      frames = info.frames;
      models = models file;
      failure = fault;
      events;
    }

  let insns_diff before after =
    let seen = Int64.Hash_set.of_list (insns before) in
    List.filter (insns after) ~f:(Fn.non (Hash_set.mem seen))
end

let spawn_thread ?stack t ~start ~arg =
  if not (paused t) then not_paused ~fn:"spawn_thread" t;
  resume t (X.Spawn (start, arg, stack));
  match t.session.spawned with Ok tid -> tid | Error msg -> failwith msg

type region = {
  lower : int64;
  upper : int64;
  readable : bool;
  writable : bool;
  executable : bool;
}

let regions t =
  if not (paused t) then not_paused ~fn:"regions" t;
  resume t X.Regions;
  List.map t.session.regions
    ~f:(fun (lower, upper, (p : Primus.Memory.protection)) ->
      {
        lower;
        upper;
        readable = p.readable;
        writable = p.writable;
        executable = p.executable;
      })

(* the bytes, that the machine, or the snapshot, stored, with the
   generated ones, if [generated] *)
let values ?(generated = false) t id =
  resume t (X.Values (id, generated));
  t.session.values

(* the addresses, coalesced into the ranges, the lowest first *)
let coalesce addrs =
  List.dedup_and_sort addrs ~compare:Int64.compare
  |> List.fold ~init:[] ~f:(fun acc a ->
      match acc with
      | (lo, n) :: rest when Int64.(lo + of_int n = a) -> (lo, n + 1) :: rest
      | _ -> (a, 1) :: acc)
  |> List.rev

(* the bytes, that differ between the stored values *)
let changed mine theirs =
  let table values =
    let t = Int64.Table.create () in
    List.iter values ~f:(fun (key, data) -> Hashtbl.set t ~key ~data);
    t
  in
  let mine = table mine and theirs = table theirs in
  let differ a b =
    Hashtbl.fold a ~init:[] ~f:(fun ~key ~data acc ->
        match Hashtbl.find b key with
        | Some x when x = data -> acc
        | _ -> key :: acc)
  in
  coalesce (differ mine theirs @ differ theirs mine)

let diff t { owner; id } =
  if not (phys_equal owner t.session) then
    invalid_arg "Bap_emu.diff: the snapshot is of another emulator";
  if not (paused t) then not_paused ~fn:"diff" t;
  let mine = values t None in
  changed mine (values t (Some id))

(* [fresh addr] unless the hook saw the instruction at [addr] last in
   the previous start of Unicorn, which stopped there, and starts there
   again, e.g., after its fault, or as the hook paused the program, so
   that the hook, that stops it, doesn't stop it again, when it
   continues *)
let instructions t =
  let last = ref None in
  fun addr ->
    let s = t.session in
    let again =
      Option.equal Int64.equal s.restarted_at (Some addr)
      &&
      match !last with
      | Some (addr', start) -> Int64.equal addr addr' && start = s.starts - 1
      | None -> false
    in
    last := Some (addr, s.starts);
    not again

(* the hook goes to the engine of the emulator, and to its new engines,
   see [X.session] *)
let installed t f =
  t.session.engine_hooks <- f :: t.session.engine_hooks;
  Option.iter t.session.active ~f

(* the hook is removed by [remove], when the innermost scope, that added
   it, ends, see [scoped], or stays *)
let scope t remove =
  match t.scopes with [] -> () | removes :: _ -> removes := remove :: !removes

let scoped t f =
  let removes = ref [] in
  t.scopes <- removes :: t.scopes;
  Exn.protect ~f ~finally:(fun () ->
      t.scopes <- List.tl_exn t.scopes;
      List.iter !removes ~f:(fun remove -> remove ()))

(* the hook of the script, which goes to the engines of the emulator, see
   [installed], and is deleted from them, when its scope ends, as the
   engines, that it was deleted from, e.g., closed ones, are gone with it *)
let hook t f =
  let hooks = ref [] in
  let install (e : X.engine) = hooks := f e @ !hooks in
  installed t install;
  scope t (fun () ->
      t.session.engine_hooks <-
        List.filter t.session.engine_hooks ~f:(fun g ->
            not (phys_equal g install));
      List.iter !hooks ~f:(fun h ->
          try Engine.delete h with Invalid_argument _ | Engine.Error _ -> ());
      hooks := [])

(* the address of the code of the instruction, without the lower bit of
   the Thumb state of ARM *)
let code_of t addr =
  match (engine t).arch with Arm -> Int64.(addr land lnot 1L) | _ -> addr

(* the instructions at the sites are seen by one hook, which the engine
   finds natively, see [Engine.on_sites] *)
let sites_hook t sites f =
  let sites = List.map sites ~f:(code_of t) in
  if not (List.is_empty sites) then
    hook t (fun e ->
        let fresh = instructions t in
        Engine.on_sites e.engine sites (fun addr _ -> if fresh addr then f addr))

let run ?until t =
  if paused t then begin
    let e = engine t in
    let hook =
      Option.map until ~f:(fun addr ->
          (* the program, which is paused at the address, runs its
             instruction first *)
          let code =
            match e.arch with Arm -> Int64.(pc t land lnot 1L) | _ -> pc t
          in
          let skip = ref (Int64.equal addr code) in
          let fresh = instructions t in
          ( e,
            Engine.on_code e.engine ~first:addr ~last:addr (fun addr _ ->
                if fresh addr then if !skip then skip := false else stop t) ))
    in
    resume t (X.Continue (pc t));
    Option.iter hook ~f:(fun (e', hook) ->
        match t.session.active with
        | Some e when phys_equal e e' -> Engine.delete hook
        | _ -> ())
  end;
  status t

let step t =
  if paused t then begin
    let e = engine t in
    let first = ref true in
    let fresh = instructions t in
    let hook =
      Engine.on_code e.engine (fun addr _ ->
          if fresh addr then if !first then first := false else stop t)
    in
    resume t (X.Continue (pc t));
    match t.session.active with
    | Some e' when phys_equal e e' -> Engine.delete hook
    | _ -> ()
  end;
  status t

let interpret t =
  if not (paused t) then not_paused ~fn:"interpret" t;
  resume t X.Interpret;
  status t

(* calls the function, and serves its pauses, at most [budget] of them,
   until it returns, or the program ends, or its [timeout] runs out, see
   [X.session.call_deadline], and gives its result, or [None], while it
   runs *)
let call_served ~fn ?budget ?timeout ?stack ?(args = []) ?(regs = []) ?thread
    ?service t addr =
  if not (paused t) then not_paused ~fn t;
  (match budget with
  | Some n when n < 0 -> invalid_argf "Bap_emu.%s: the budget is %d" fn n ()
  | _ -> ());
  (match timeout with
  | Some s when Float.(s < 0. || is_nan s) ->
      invalid_argf "Bap_emu.%s: the timeout is %g" fn s ()
  | _ -> ());
  t.session.called <- None;
  t.session.call_deadline <- Option.map timeout ~f:(fun s -> X.clock () +. s);
  (* the call, whose time ran out, isn't served, as it would run on *)
  let expired () =
    Option.is_some timeout && Option.is_none t.session.call_deadline
  in
  let rec serve served =
    match (t.session.called, service, status t) with
    | None, Some service, Paused
      when Option.for_all budget ~f:(fun n -> served < n) && not (expired ()) ->
        service t (pc t);
        ignore (run t : status);
        serve (served + 1)
    | _ -> ()
  in
  Exn.protect
    ~f:(fun () ->
      resume t (X.Call (addr, args, regs, thread, stack));
      serve 0)
    ~finally:(fun () -> t.session.call_deadline <- None);
  match t.session.called with
  | Some (Ok x) -> Some x
  | Some (Error msg) -> failwithf "Bap_emu.%s: %s" fn msg ()
  | None -> None

let call ?stack ?args ?regs ?thread ?service t addr =
  call_served ~fn:"call" ?stack ?args ?regs ?thread ?service t addr

let returned t = match t.session.called with Some (Ok x) -> Some x | _ -> None
let registers t = Target.Regs.names (engine t).regs

let reg t name =
  match Target.Regs.read_name (engine t).regs name with
  | Some x -> Bitvec.to_int64 (Word.to_bitvec x)
  | None -> invalid_argf "Bap_emu: unknown register %s" name ()

let set_reg t name x =
  if not (Target.Regs.write_name (engine t).regs name (Word.of_int64 x)) then
    invalid_argf "Bap_emu: unknown register %s" name ()

let reg_word t name =
  match Target.Regs.read_name (engine t).regs name with
  | Some x -> x
  | None -> invalid_argf "Bap_emu: unknown register %s" name ()

let set_reg_word t name x =
  if not (Target.Regs.write_name (engine t).regs name x) then
    invalid_argf "Bap_emu: unknown register %s" name ()

(* the pages, which a paused program copies to Unicorn, as Primus has
   them *)
let rec accessible t addr n f =
  match f () with
  | x -> x
  | exception Native.Missing missing when paused t ->
      let page = X.page_of missing in
      resume t (X.Map missing);
      if Hashtbl.mem (engine t).pages page then accessible t addr n f
      else invalid_argf "Bap_emu: %Lx is not mapped" missing ()
  | exception Native.Missing missing ->
      invalid_argf
        "Bap_emu: the page of %Lx is not in Unicorn yet, as the program runs, \
         e.g., in a hook; pause it to read the page, see Bap_emu.defer"
        missing ()
  | exception Native.Denied ->
      invalid_argf "Bap_emu: the access to %d bytes at %Lx is denied" n addr ()

(* the component runs in the machine, which is paused, or ended *)
let primus t component =
  match t.state with
  | Suspended _ | Ended _ -> resume t (X.Run component)
  | _ -> not_paused ~fn:"primus" t

(* the bytes, that Primus has, and Unicorn doesn't, as their page is
   marked, e.g., tainted, see [X.ensure_page] *)
let primus_bytes t addr n =
  let result = ref None in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                module Memory = Primus.Memory.Make (Machine)
                open Machine.Syntax

                let init () =
                  let width = (engine t).bytes * 8 in
                  Memory.load_bytes (Word.of_int64 ~width addr) n
                  >>| fun loaded ->
                  if
                    Array.for_all loaded ~f:(function
                      | Some (_, (p : Primus.Memory.protection)) -> p.readable
                      | None -> false)
                  then
                    result :=
                      Some
                        (String.of_array
                           (Array.map loaded ~f:(fun b ->
                                fst (Option.value_exn b))))
              end);
  !result

type provenance = Stored | Generated | Mapped | Unmapped

let provenance t addr =
  if not (paused t) then not_paused ~fn:"provenance" t;
  let width = (engine t).bytes * 8 in
  let result = ref Unmapped in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                module Memory = Primus.Memory.Make (Machine)
                open Machine.Syntax

                let init () =
                  Memory.origin (Word.of_int64 ~width addr) >>| fun origin ->
                  result :=
                    match origin with
                    | Primus.Memory.Stored -> Stored
                    | Generated -> Generated
                    | Mapped -> Mapped
                    | Unmapped -> Unmapped
              end);
  !result

let find_bytes ?(provenance = [ Stored; Mapped ]) t ~pattern ~ranges =
  if String.is_empty pattern then
    invalid_arg "Bap_emu.find_bytes: the pattern is empty";
  if not (paused t) then not_paused ~fn:"find_bytes" t;
  let width = (engine t).bytes * 8 in
  let result = ref [] in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                module Memory = Primus.Memory.Make (Machine)
                open Machine.Syntax

                let init () =
                  let origins =
                    List.map provenance ~f:(function
                      | Stored -> Primus.Memory.Stored
                      | Generated -> Generated
                      | Mapped -> Mapped
                      | Unmapped -> Unmapped)
                  in
                  let addr = Word.of_int64 ~width in
                  let ranges =
                    List.map ranges ~f:(fun (lower, upper) ->
                        (addr lower, addr upper))
                  in
                  Memory.find_bytes ~pattern ~origins ~ranges >>| fun hits ->
                  result := List.map hits ~f:Word.to_int64_exn
              end);
  !result

type change = {
  addr : int64;
  size : int;
  before : provenance;
  after : provenance;
}

(* where the bytes come from, in the machine, or in the snapshot *)
let origins t id addrs =
  resume t (X.Origins (id, addrs));
  List.map t.session.origins ~f:(function
    | Primus.Memory.Stored -> Stored
    | Generated -> Generated
    | Mapped -> Mapped
    | Unmapped -> Unmapped)

let changes t ({ id; _ } as snapshot) =
  let ranges = diff t snapshot in
  let addrs =
    List.concat_map ranges ~f:(fun (a, n) ->
        List.init n ~f:(fun i -> Int64.(a + of_int i)))
  in
  let before = origins t (Some id) addrs and after = origins t None addrs in
  List.zip_exn addrs (List.zip_exn before after)
  |> List.fold ~init:[] ~f:(fun acc (addr, (before, after)) ->
      match acc with
      | c :: rest
        when Int64.(c.addr + of_int c.size = addr)
             && Poly.equal c.before before && Poly.equal c.after after ->
          { c with size = c.size + 1 } :: rest
      | _ -> { addr; size = 1; before; after } :: acc)
  |> List.rev

let read t addr n =
  match accessible t addr n (fun () -> X.engine_read (engine t) addr n) with
  | data -> data
  | exception (Invalid_argument _ as exn)
    when match t.state with Suspended _ | Ended _ -> true | _ -> false -> (
      match primus_bytes t addr n with Some data -> data | None -> raise exn)

(* the bytes go only to Unicorn, which translates the code anew, see
   [X.engine_write] *)
let write_direct t addr data =
  let n = String.length data in
  accessible t addr n (fun () ->
      let e = engine t in
      if X.engine_readable e addr n < n then raise Native.Denied;
      X.engine_write e addr data)

(* the bytes go to Primus, from which they go to Unicorn, see
   [X.backing], and the code, that it translated, is translated anew *)
let write t addr data =
  if not (paused t) then not_paused ~fn:"write" t;
  (* the bytes are mapped and readable *)
  ignore (read t addr (String.length data) : string);
  resume t (X.Store (addr, data))

(* The instructions of an IT block of Thumb have the conditions, that
   the decoder of LLVM keeps, as it decodes the IT instruction, and the
   next ones, so the instruction of the block is lifted after them, from
   the IT instruction, at most 4 instructions before it, and the members
   after it are lifted then, so that the decoder leaves the block, as it
   does, when the IT instruction itself is lifted.

   [it_blocks read addr] the blocks, that the instruction at [addr] may
   be in, the nearest first, as a halfword, that looks like an IT
   instruction, may be the second one of a 32-bit instruction, see
   [lift_in_it_block]: the address of the IT instruction, the
   instructions, whose bytes [read addr n] reads, before the instruction
   at [addr], and the ones after it, by their addresses and bytes. *)
let halfword read a =
  match read a 2 with
  | b when String.length b = 2 ->
      Some (Char.to_int b.[0] lor (Char.to_int b.[1] lsl 8))
  | _ -> None

(* the size of the instruction of Thumb at [a], whose halfword [read a 2]
   reads: the 32-bit instructions start with 0b11101, 0b11110, or
   0b11111 *)
let thumb_size read a =
  match halfword read a with
  | Some h when h lsr 11 >= 0b11101 -> Some 4
  | Some _ -> Some 2
  | None -> None

let it_blocks read addr =
  let halfword = halfword read and size = thumb_size read in
  let members it =
    match halfword it with
    | Some h when h land 0xFF00 = 0xBF00 && h land 0xF <> 0 ->
        Some (4 - Int.ctz (h land 0xF))
    | _ -> None
  in
  (* the [n] instructions from [a] *)
  let rec next a n acc =
    match size a with
    | Some k when n > 0 ->
        next Int64.(a + of_int k) (n - 1) ((a, read a k) :: acc)
    | _ -> List.rev acc
  in
  (* the instructions from [a], before [addr], and the ones after it, if
     one of the [n] members of the block is at [addr] *)
  let rec walk a n acc =
    if n = 0 || Int64.(a > addr) then None
    else
      match size a with
      | None -> None
      | Some k when Int64.(a = addr) ->
          Some (List.rev acc, next Int64.(a + of_int k) (n - 1) [])
      | Some k -> walk Int64.(a + of_int k) (n - 1) ((a, read a k) :: acc)
  in
  List.range 0 8
  |> List.filter_map ~f:(fun i ->
      let it = Int64.(addr - of_int Int.(2 * i)) in
      match members it with
      | None -> None
      | Some n when i = 0 -> Some (it, [], next Int64.(it + 2L) n [])
      | Some n ->
          walk Int64.(it + 2L) n [ (it, read it 2) ]
          |> Option.map ~f:(fun (before, after) -> (it, before, after)))

(* the instruction at [addr], whose bytes are [bytes], lifted in its IT
   block, see [it_blocks_of], the instructions before it and after it,
   or lifted as it is, if there is none. The instructions of the block
   are decoded, rather than taken from the disassembly, so that the
   decoder is in the state of the block, when it decodes each of them. *)
let lift_in_it_block ?encoding proj block addr bytes =
  let open Knowledge.Syntax in
  let decode =
    Knowledge.List.map ~f:(fun (a, code) ->
        Primus.Lift.instruction ?encoding ~disassembled:false proj a code
        >>| fun insn -> (a, code, insn))
  in
  match block with
  | None ->
      Primus.Lift.instruction ?encoding proj addr bytes >>| fun insn ->
      (insn, [])
  | Some (before, after) ->
      decode before >>= fun before ->
      Primus.Lift.instruction ?encoding ~disassembled:false proj addr bytes
      >>= fun insn ->
      decode after >>| fun after -> (insn, before @ after)

(* the instructions of Thumb at [addr], whose bytes are [bytes], and the
   others of its IT block, that were decoded with it, see
   [lift_in_it_block], are cached in [lifts], and known as the
   instructions, see [it_blocks_of] *)
let remember t lifts addr bytes others =
  Hashtbl.set t.thumb_insns ~key:addr ~data:(String.prefix bytes 2);
  List.iter others ~f:(fun (a, code, insn) ->
      Hashtbl.set lifts ~key:(a, code, true) ~data:insn;
      Hashtbl.set t.thumb_insns ~key:a ~data:(String.prefix code 2))

(* the IT block of Thumb, that the instruction at [addr] is in, if
   [thumb], the first of [it_blocks], whose IT instruction is an
   instruction, as the instructions from the farthest known one before
   it, within the reach of an IT block, see [insns] and [thumb_insns],
   e.g., the ones, that the hooks before saw, reach it, so that the
   second halfword of a 32-bit instruction, that looks like an IT
   instruction, is not one; the first, if none is known: the instructions
   before the one at [addr], and the ones after it *)
let it_blocks_of t ~thumb addr =
  if not thumb then None
  else
    let read a n = try read t a n with Invalid_argument _ -> "" in
    let known a =
      (match Hashtbl.find t.thumb_insns a with
        | Some halfword -> String.equal halfword (read a 2)
        | None -> false)
      || Hash_set.mem (Lazy.force t.insns) a
    in
    (* the instructions from [a], that reach [addr] *)
    let rec walk a acc =
      if Int64.(a = addr) then Some acc
      else if Int64.(a > addr) then None
      else
        match thumb_size read a with
        | Some n -> walk Int64.(a + of_int n) (a :: acc)
        | None -> None
    in
    (* the instructions from the farthest known one, that reach [addr] *)
    let rec starts a =
      if Int64.(a >= addr) then None
      else
        match if known a then walk a [] else None with
        | Some starts -> Some starts
        | None -> starts Int64.(a + 2L)
    in
    let blocks = it_blocks read addr in
    let blocks =
      match starts Int64.(addr - 16L) with
      | None -> blocks
      | Some starts ->
          List.filter blocks ~f:(fun (it, _, _) ->
              List.mem starts it ~equal:Int64.equal)
    in
    List.hd blocks |> Option.map ~f:(fun (_, before, after) -> (before, after))

(* the instruction in a hook, while the machine runs the program, is
   lifted outside of it, as the script does, in the knowledge, that
   starts from the toplevel one, and keeps the semantics, e.g., the Lisp
   program of x86, which it loads once, and the instructions, which are
   cached by their addresses and bytes; the IT block, see [it_blocks_of],
   is looked for, when the instruction is not cached *)
let hooked t ?encoding ~thumb ~block addr bytes =
  let key = (addr, bytes, thumb) in
  match Hashtbl.find t.lifted key with
  | Some insn -> insn
  | None ->
      let toplevel = Toplevel.current () in
      let result = ref None in
      Toplevel.set (Option.value t.hooked ~default:toplevel);
      let started = Caml_unix.gettimeofday () in
      Exn.protect
        ~finally:(fun () ->
          (* the knowledge after the lifts, that take long, e.g., the
             first one, which loads the semantics, is kept, and the one
             after the others is dropped, so that it doesn't grow with
             the instructions, that are lifted, which it would keep *)
          if
            Option.is_none t.hooked
            || Float.(Caml_unix.gettimeofday () -. started > 0.1)
          then t.hooked <- Some (Toplevel.current ());
          Toplevel.set toplevel)
        ~f:(fun () ->
          Toplevel.exec
            Knowledge.Syntax.(
              lift_in_it_block ?encoding t.project (block ()) addr bytes
              >>| fun (insn, others) ->
              result := insn;
              if thumb then remember t t.lifted addr bytes others));
      Hashtbl.set t.lifted ~key ~data:!result;
      !result

(* the bytes are read before the instruction is lifted in the machine,
   as the reading may copy the pages to Unicorn, and the instruction may
   end on an unmapped page *)
let bir ?thumb t addr =
  let e = engine t in
  let thumb =
    match (e.arch, thumb) with
    | Arm, Some thumb -> thumb
    | Arm, None -> Int64.(addr land 1L = 1L)
    | _ -> false
  in
  let addr = match e.arch with Arm -> Int64.(addr land lnot 1L) | _ -> addr in
  let bytes =
    List.range ~stride:(-1) Primus.Lift.max_size 0
    |> List.find_map ~f:(fun n ->
        try Some (read t addr n) with Invalid_argument _ -> None)
    |> Option.value_exn ~message:(sprintf "Bap_emu.bir: %Lx is not mapped" addr)
  in
  let block () = it_blocks_of t ~thumb addr in
  let read a n =
    let off = Int64.(to_int_exn (a - addr)) in
    if off < 0 || off >= String.length bytes then ""
    else String.sub bytes ~pos:off ~len:(min n (String.length bytes - off))
  in
  let encoding =
    match e.arch with Arm -> Primus.Interworking.encoding ~thumb | _ -> None
  in
  match t.state with
  | Running -> hooked t ?encoding ~thumb ~block addr bytes
  | _ ->
      Hashtbl.find_or_add t.paused_lifts (addr, bytes, thumb)
        ~default:(fun () ->
          let result = ref None in
          let block = block () in
          primus t
            (module functor
                      (Machine : Primus.Machine.S)
                      ->
                      struct
                        module Lift = Primus.Lift.Make (Machine)
                        open Machine.Syntax

                        let init () =
                          Machine.get () >>= fun proj ->
                          (match block with
                            | None ->
                                Lift.insn ?encoding ~read addr >>| fun insn ->
                                (insn, [])
                            | Some _ ->
                                Machine.knowledge
                                  (lift_in_it_block ?encoding proj block addr
                                     bytes))
                          >>| fun (insn, others) ->
                          result := insn;
                          if thumb then
                            remember t t.paused_lifts addr bytes others
                      end);
          !result)

(* the bytes of the code at [addr], at most the size of an instruction,
   fewer, if the rest is not mapped *)
let code_bytes t addr =
  List.range ~stride:(-1) Primus.Lift.max_size 0
  |> List.find_map ~f:(fun n ->
      try Some (read t addr n) with Invalid_argument _ -> None)
  |> Option.value ~default:""

(* the instruction at [pc], lifted outside of the machine, as in the
   hooks, from [bytes], by default, that it has now, in the mode, e.g.,
   Thumb or A32 of ARM, as the target doesn't know it *)
let lift ?(thumb = false) ?bytes t pc =
  let bytes = match bytes with Some b -> b | None -> code_bytes t pc in
  let encoding =
    match (engine t).arch with
    | Arm -> Primus.Interworking.encoding ~thumb
    | _ -> None
  in
  hooked t ?encoding ~thumb ~block:(fun () -> it_blocks_of t ~thumb pc) pc bytes

(* the instruction, that the lifted engine ran, at the address, from the
   bytes, that it had, when it was lifted, which the engine keeps, as
   the memory may not have them anymore, e.g., when the program scrubbed
   the code, that it unpacked, see [X.lifter] *)
type executed = {
  bytes : string;
  name : string;
  thumb : bool;
  bir : blk term list;
}

(* the architecture of the engine, also after the program ended, when
   there is no engine *)
let arch t =
  match t.session.active with
  | Some e -> e.arch
  | None -> (
      match Target.engine t.target with
      | Some (arch, _) -> arch
      | None -> invalid_arg "Bap_emu: the target has no engine")

let executed_at ?thumb t pc =
  let thumb, pc =
    match (arch t, thumb) with
    | Arm, Some thumb -> (thumb, Int64.(pc land lnot 1L))
    | Arm, None -> (Int64.(pc land 1L = 1L), Int64.(pc land lnot 1L))
    | _ -> (false, pc)
  in
  (* the engine, that runs, has the instruction, unless it dropped
     them, e.g., when the script wrote the code, after which the lifter
     has the last one, that was lifted, until the engine lifts it anew *)
  match
    Option.bind t.session.active ~f:(fun e -> Engine.insn_at e.engine pc)
  with
  | Some (bytes, name, thumb', bir) when Bool.equal thumb thumb' ->
      Some { bytes; name; thumb; bir }
  | _ -> (
      match Option.bind t.session.lifter ~f:(fun l -> l.lifted ~thumb pc) with
      | Some (e : X.Lifts.entry) ->
          Some { bytes = e.code; name = e.name; thumb = e.thumb; bir = e.blks }
      | None ->
          (* the instruction ran before the checkpoint, from which the
             program continues, and is lifted anew from its bytes, that
             the checkpoint keeps *)
          Option.both t.session.lifter
            (Hashtbl.find t.session.ran_before (pc, thumb))
          |> Option.bind ~f:(fun ((l : X.lifter), code) ->
              Option.map (l.lift ~thumb pc code) ~f:(fun (size, name, bir) ->
                  { bytes = String.prefix code size; name; thumb; bir })))

let insn_at ?thumb t pc = executed_at ?thumb t pc

let lift_with_history ?bytes ?(executed_bytes = false) ~thumb t pc =
  match lift ?bytes ~thumb t pc with
  | Some (size, blks) when size > 0 && not (List.is_empty blks) ->
      Some (size, blks)
  | _ when executed_bytes -> (
      match executed_at ~thumb t pc with
      | Some { bytes; bir; _ }
        when (not (String.is_empty bytes)) && not (List.is_empty bir) ->
          Some (String.length bytes, bir)
      | _ -> None)
  | _ -> None

(* the addresses of the instructions, that the lifted engine ran, also
   before the checkpoint, from which the program continues, with the
   lower bit set in the Thumb state of ARM *)
let insns t =
  let addr (pc, thumb) = if thumb then Int64.(pc lor 1L) else pc in
  let ran = Hash_set.Poly.create () in
  Hashtbl.iter_keys t.session.ran_before ~f:(fun k -> Hash_set.add ran (addr k));
  Option.iter t.session.lifter ~f:(fun (l : X.lifter) ->
      List.iter (l.ran ()) ~f:(fun (pc, thumb, _) ->
          Hash_set.add ran (addr (pc, thumb))));
  Option.iter t.session.active ~f:(fun e ->
      List.iter (Engine.insn_addrs e.engine) ~f:(fun pc ->
          match Engine.insn_at e.engine pc with
          | Some (_, _, thumb, _) -> Hash_set.add ran (addr (pc, thumb))
          | None -> ()));
  Hash_set.to_list ran |> List.sort ~compare:Int64.compare

(* the instructions, that ran since the checkpoint was saved, that the
   checkpoint doesn't have *)
let insns_since t file =
  let seen = Int64.Hash_set.of_list (Checkpoint.insns file) in
  List.filter (insns t) ~f:(Fn.non (Hash_set.mem seen))

(* the bytes of the instructions, that ran, from the address, one after
   another, as far as they go, at most [n] *)
let lifted_bytes ?thumb t addr n =
  let thumb =
    match (arch t, thumb) with
    | Arm, Some thumb -> thumb
    | Arm, None -> Int64.(addr land 1L = 1L)
    | _ -> false
  in
  let addr = match arch t with Arm -> Int64.(addr land lnot 1L) | _ -> addr in
  let buf = Buffer.create n in
  let rec collect addr =
    if Buffer.length buf < n then
      match executed_at ~thumb t addr with
      | Some { bytes; _ } when not (String.is_empty bytes) ->
          Buffer.add_string buf bytes;
          collect Int64.(addr + of_int (String.length bytes))
      | _ -> ()
  in
  collect addr;
  String.prefix (Buffer.contents buf) n

type decode_failure = {
  index : int64;
  pc : int64;
  block : int64 option;
  thread : int;
}

module Trace = struct
  type emu = t

  type t = {
    emu : emu;
    trace : Engine.Trace.t;
    memory : bool;
        (** if all accesses are recorded, which the slices follow, not only the
            ones, that the trace watches *)
    watch : (int64 * int64) option;
    mutable active : bool;
    mutable hooks : Engine.hook list option;
    blocks : (int * int64 array) list Int64.Table.t;
        (** the instructions of the blocks, by their addresses, with the lower
            bit of Thumb, and sizes, see [insns] *)
  }

  (* the hooks are native, see [Engine.trace], and go to the new engines too,
     until the trace stops *)
  let start ?(size = 1 lsl 20) ?every ?(blocks = false) ?(accesses = 0)
      ?(read_values = false) ?watch ?first ?last emu =
    let accesses =
      if Option.is_some watch && accesses = 0 then 1 lsl 16 else accesses
    in
    let memory = accesses > 0 in
    if
      memory
      && (Option.value every ~default:1 > 1
         || Option.is_some first || Option.is_some last)
    then
      invalid_arg
        "Bap_emu.Trace.start: the accesses are recorded only with all \
         instructions, or blocks";
    let trace =
      Engine.Trace.create ?every ~blocks ~accesses ~read_values size
    in
    let blocks = Int64.Table.create () in
    let t =
      {
        emu;
        trace;
        memory = memory && Option.is_none watch;
        watch;
        active = true;
        hooks = None;
        blocks;
      }
    in
    let owned_trace = Weak.create 1 and owned_blocks = Weak.create 1 in
    Weak.set owned_trace 0 (Some trace);
    Weak.set owned_blocks 0 (Some blocks);
    emu.traces <- (owned_trace, owned_blocks) :: emu.traces;
    installed emu (fun e ->
        if t.active then
          t.hooks <-
            Some (Engine.trace ?first ?last ?watch ~memory e.engine trace));
    t

  (* the hooks of a closed engine are gone with it *)
  let stop t =
    if t.active then begin
      t.active <- false;
      Option.iter t.hooks ~f:(fun hooks ->
          List.iter hooks ~f:(fun hook ->
              try Engine.delete hook with Invalid_argument _ -> ()));
      t.hooks <- None
    end

  let count t = Engine.Trace.count t.trace
  let retained t = Engine.Trace.retained t.trace
  let clear t = Engine.Trace.clear t.trace
  let blocks t = Engine.Trace.blocks t.trace
  let pcs ?last t = Engine.Trace.pcs ?last t.trace
  let tids ?last t = Engine.Trace.tids ?last t.trace
  let sizes ?last t = Engine.Trace.sizes ?last t.trace
  let save ?last t file = Engine.Trace.save ?last t.trace file

  type access = {
    insn : int64;
    pc : int64;
    addr : int64;
    size : int;
    write : bool;
    value : int64;
    old : int64;
    read_value : int64 option;
    thread : int;
  }

  let access rows i =
    let open Bigarray.Array2 in
    let info = get rows i 3 in
    {
      insn = get rows i 0;
      addr = get rows i 1;
      value = get rows i 2;
      read_value =
        (if Int64.(shift_right_logical info 33 land 1L = 1L) then
           Some (get rows i 2)
         else None);
      size = Int64.(to_int_exn (info land 0xFFFF_FFFFL));
      write = Int64.(shift_right_logical info 32 land 1L = 1L);
      pc = get rows i 4;
      old = get rows i 5;
      thread = Int64.to_int_exn (get rows i 6);
    }

  let accesses ?last t =
    let rows = Engine.Trace.accesses ?last t.trace in
    List.init (Bigarray.Array2.dim1 rows) ~f:(access rows)

  (* the [top] values, that occur most, with their numbers, the most
     first, and the lower first, of the same number *)
  let most ?top counts =
    let all =
      Hashtbl.to_alist counts
      |> List.sort ~compare:(fun (a, n) (b, m) ->
          match Int.compare m n with 0 -> Int64.compare a b | c -> c)
    in
    match top with Some n -> List.take all n | None -> all

  let hot ?last ?top t =
    let pcs = pcs ?last t in
    let counts = Int64.Table.create () in
    for i = 0 to Bigarray.Array1.dim pcs - 1 do
      Hashtbl.incr counts (Bigarray.Array1.get pcs i)
    done;
    most ?top counts

  let addresses ?last ?top t =
    let reads = Int64.Table.create () and writes = Int64.Table.create () in
    List.iter (accesses ?last t) ~f:(fun a ->
        Hashtbl.incr (if a.write then writes else reads) a.addr);
    let counts = Int64.Table.create () in
    Hashtbl.iteri reads ~f:(fun ~key ~data ->
        Hashtbl.update counts key ~f:(fun n -> Option.value n ~default:0 + data));
    Hashtbl.iteri writes ~f:(fun ~key ~data ->
        Hashtbl.update counts key ~f:(fun n -> Option.value n ~default:0 + data));
    most ?top counts
    |> List.map ~f:(fun (addr, _) ->
        ( addr,
          Option.value (Hashtbl.find reads addr) ~default:0,
          Option.value (Hashtbl.find writes addr) ~default:0 ))

  (* the instructions of the block of [size] bytes at [addr], in the
     mode, which are decoded once, as the sizes of the instructions, that
     are lifted, and the instruction, at which decoding failed *)
  let block t ~executed_bytes ~thumb addr size =
    let key = if thumb then Int64.(addr lor 1L) else addr in
    let known =
      if executed_bytes then []
      else Option.value (Hashtbl.find t.blocks key) ~default:[]
    in
    match List.Assoc.find known size ~equal:Int.equal with
    | Some insns -> (insns, None)
    | None ->
        let last = Int64.(addr + of_int size) in
        (* the block, whose instruction can't be lifted, e.g., as its
           page isn't in Unicorn yet, ends there, and isn't cached, so
           that it is decoded again *)
        let rec loop pc acc =
          if Int64.(pc >= last) then (Array.of_list_rev acc, None)
          else
            match lift_with_history ~executed_bytes ~thumb t.emu pc with
            | Some (n, _) when n > 0 -> loop Int64.(pc + of_int n) (pc :: acc)
            | _ -> (Array.of_list_rev (pc :: acc), Some pc)
        in
        let insns, failed = loop addr [] in
        (* recovered instructions don't enter the current-byte cache *)
        if Option.is_none failed && not executed_bytes then
          Hashtbl.set t.blocks ~key ~data:((size, insns) :: known);
        (insns, failed)

  type words = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t

  let words n : words =
    Bigarray.Array1.create Bigarray.int64 Bigarray.c_layout n

  type decode_status = Decoded | Decode_failed

  type window_instruction = {
    index : int64;
    pc : int64;
    block : int64 option;
    thread : int;
    decode : decode_status;
  }

  type expanded_window = {
    pcs : words;
    records : words;
    modes : Engine.Trace.modes;
    tids : words;
    sources : int64 option array;
    failures : decode_failure list;
  }

  (* the program counters of the instructions of the last [last] records,
     their global record indices, modes, and TIDs, also of the instructions,
     into which the blocks expand *)
  let expanded_window ?(records = true) ?(executed_bytes = false) ?thread ?last
      t =
    let raw_pcs = pcs ?last t in
    let raw_tids = tids ?last t in
    let raw_modes = Engine.Trace.modes ?last t.trace in
    let raw_n = Bigarray.Array1.dim raw_pcs in
    let first = Int64.(count t - of_int raw_n) in
    let selected =
      Array.init raw_n ~f:Fn.id
      |> Array.filter ~f:(fun i ->
          Option.for_all thread ~f:(fun tid ->
              Int64.equal
                (Bigarray.Array1.unsafe_get raw_tids i)
                (Int64.of_int tid)))
    in
    let n = Array.length selected in
    let pcs = words n and selected_tids = words n in
    let modes =
      Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout n
    in
    Array.iteri selected ~f:(fun i raw ->
        Bigarray.Array1.unsafe_set pcs i
          (Bigarray.Array1.unsafe_get raw_pcs raw);
        Bigarray.Array1.unsafe_set selected_tids i
          (Bigarray.Array1.unsafe_get raw_tids raw);
        Bigarray.Array1.unsafe_set modes i
          (Bigarray.Array1.unsafe_get raw_modes raw));
    if not (blocks t) then begin
      let indices = words (if records then n else 0) in
      if records then
        Array.iteri selected ~f:(fun i raw ->
            Bigarray.Array1.unsafe_set indices i Int64.(first + of_int raw));
      {
        pcs;
        records = indices;
        modes;
        tids = selected_tids;
        sources = Array.create ~len:n None;
        failures = [];
      }
    end
    else
      let sizes = sizes ?last t in
      (* the blocks of the loops repeat, so they are cached by the lower
         bits of their addresses first *)
      let slots = 4096 in
      let cache = Array.create ~len:slots (-1L, -1, [||], None) in
      let expanded =
        Array.init n ~f:(fun i ->
            let thumb = Bigarray.Array1.unsafe_get modes i = 1 in
            let addr = Bigarray.Array1.unsafe_get pcs i in
            let key = if thumb then Int64.(addr lor 1L) else addr in
            let size =
              Int32.to_int_trunc
                (Bigarray.Array1.unsafe_get sizes (Array.unsafe_get selected i))
            in
            let slot = Int64.to_int_trunc key land (slots - 1) in
            let a, sz, b, failed = Array.unsafe_get cache slot in
            if Int64.(a = key) && sz = size then (b, failed)
            else
              let b, failed = block t ~executed_bytes ~thumb addr size in
              Array.unsafe_set cache slot (key, size, b, failed);
              (b, failed))
      in
      let total =
        Array.sum (module Int) expanded ~f:(fun (b, _) -> Array.length b)
      in
      let out = words total
      and out_tids = words total
      and indices = words (if records then total else 0)
      and decoded_modes =
        Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout total
      in
      let sources = Array.create ~len:total None in
      let failures = ref [] and pos = ref 0 in
      Array.iteri expanded ~f:(fun i (b, failed) ->
          let record = Int64.(first + of_int (Array.unsafe_get selected i)) in
          let mode = Bigarray.Array1.unsafe_get modes i in
          let tid = Bigarray.Array1.unsafe_get selected_tids i in
          let addr = Bigarray.Array1.unsafe_get pcs i in
          for j = 0 to Array.length b - 1 do
            Bigarray.Array1.unsafe_set out (!pos + j) (Array.unsafe_get b j);
            Bigarray.Array1.unsafe_set out_tids (!pos + j) tid;
            Bigarray.Array1.unsafe_set decoded_modes (!pos + j) mode;
            if records then Bigarray.Array1.unsafe_set indices (!pos + j) record;
            Array.unsafe_set sources (!pos + j) (Some addr)
          done;
          Option.iter failed ~f:(fun pc ->
              failures :=
                {
                  index = record;
                  pc;
                  block = Some addr;
                  thread = Int64.to_int_exn tid;
                }
                :: !failures);
          pos := !pos + Array.length b);
      {
        pcs = out;
        records = indices;
        modes = decoded_modes;
        tids = out_tids;
        sources;
        failures = List.rev !failures;
      }

  let window ?(records = true) ?thread ?last t :
      words * words * Engine.Trace.modes * words =
    let w = expanded_window ~records ?thread ?last t in
    (w.pcs, w.records, w.modes, w.tids)

  let inspect ?(executed_bytes = false) ?thread ?last t =
    let w = expanded_window ~executed_bytes ?thread ?last t in
    let failed = Hashtbl.Poly.create () in
    List.iter w.failures ~f:(fun f ->
        Hashtbl.add_exn failed ~key:(f.index, f.pc) ~data:());
    List.init (Bigarray.Array1.dim w.pcs) ~f:(fun i ->
        let index = Bigarray.Array1.unsafe_get w.records i in
        let pc = Bigarray.Array1.unsafe_get w.pcs i in
        let thumb = Bigarray.Array1.unsafe_get w.modes i = 1 in
        let decode =
          if Hashtbl.mem failed (index, pc) then Decode_failed
          else if blocks t then Decoded
          else
            match lift_with_history ~executed_bytes ~thumb t.emu pc with
            | Some (size, _) when size > 0 -> Decoded
            | _ -> Decode_failed
        in
        {
          index;
          pc;
          block = Array.unsafe_get w.sources i;
          thread = Int64.to_int_exn (Bigarray.Array1.unsafe_get w.tids i);
          decode;
        })

  let insns ?last t =
    if blocks t then
      let pcs, _, _, _ = window ~records:false ?last t in
      pcs
    else pcs ?last t

  (* the calls of the instructions of the last [last] records, by their
     sites, with the addresses, that they called, which the next
     instructions are at, and how many times, the most often first: an
     instruction calls, if its IR has a call, e.g., call of x86, or bl
     of ARM, which is checked once per instruction, and the call, whose
     next instruction is the one after it, isn't taken, e.g., a
     conditional one *)
  (* the registers at the sites, which the hooks of the sites record,
     see [Bap_emu.on_code], in a ring of their own *)
  type capture = {
    entries : (int64 * int64 list) Queue.t;
    limit : int;
    mutable total : int64;
    mutable recording : bool;
  }

  (* the registers, that the C ABI of the target passes the arguments in,
     in their order *)
  let argument_registers target =
    match Bap_c.Std.C.Abi.lookup target with
    | None -> []
    | Some abi ->
        let long = Bap_c.Std.C.Type.basic `slong in
        let proto : Bap_c.Std.C.Type.proto =
          {
            return = long;
            args = List.init 8 ~f:(fun i -> (sprintf "a%d" i, long));
            variadic = false;
          }
        in
        Bap_c.Std.C.Abi.apply abi
          (Bap_c.Std.C.Abi.model target)
          [] proto (Sub.create ())
        |> Term.enum arg_t |> Seq.to_list
        |> List.filter_map ~f:(fun a ->
            match (Arg.intent a, Arg.rhs a) with
            | Some In, Var v -> Some (Var.name v)
            | Some In, (Cast (_, _, Var v) | Extract (_, _, Var v)) ->
                Some (Var.name v)
            | _ -> None)

  let capture ?(size = 1 lsl 16) ?regs emu sites =
    let regs =
      match regs with
      | Some regs -> regs
      | None -> argument_registers emu.target
    in
    let c =
      { entries = Queue.create (); limit = size; total = 0L; recording = true }
    in
    (* the site, as the script gave it, e.g., with the lower bit of
       Thumb, by the address of its code *)
    let given = Int64.Table.create () in
    List.iter sites ~f:(fun site ->
        Hashtbl.set given ~key:(code_of emu site) ~data:site);
    sites_hook emu sites (fun addr ->
        if c.recording then begin
          if Queue.length c.entries >= c.limit then
            ignore (Queue.dequeue_exn c.entries : int64 * int64 list);
          let site = Option.value (Hashtbl.find given addr) ~default:addr in
          Queue.enqueue c.entries (site, List.map regs ~f:(reg emu));
          c.total <- Int64.succ c.total
        end);
    c

  let stop_capture c = c.recording <- false
  let captures c = c.total

  let captured ?last c =
    let all = Queue.to_list c.entries in
    match last with
    | Some n when n < List.length all -> List.drop all (List.length all - n)
    | _ -> all

  type call = Bap_emu_xrefs.call = {
    site : int64;
    targets : (int64 * int) list;
    thread : int;
  }

  let calls ?thread ?last t =
    let pcs, _, modes, tids = window ?thread ?last t in
    let sizes = Int64.Table.create () in
    let calling thumb pc =
      let key = if thumb then Int64.(pc lor 1L) else pc in
      Hashtbl.find_or_add sizes key ~default:(fun () ->
          match lift ~thumb t.emu pc with
          | Some (size, blks)
            when List.exists blks ~f:(fun blk ->
                     Term.enum jmp_t blk
                     |> Seq.exists ~f:(fun jmp ->
                         match Jmp.kind jmp with Call _ -> true | _ -> false))
            ->
              Some size
          | _ -> None)
    in
    let sites = Hashtbl.Poly.create () in
    for i = 0 to Bigarray.Array1.dim pcs - 2 do
      let pc = Bigarray.Array1.unsafe_get pcs i in
      let thumb = Bigarray.Array1.unsafe_get modes i = 1 in
      let tid = Bigarray.Array1.unsafe_get tids i in
      if Int64.equal tid (Bigarray.Array1.unsafe_get tids (i + 1)) then
        match calling thumb pc with
        | Some size ->
            let next = Bigarray.Array1.unsafe_get pcs (i + 1) in
            if Int64.(next <> pc + of_int size) then
              Hashtbl.update sites
                (Int64.to_int_exn tid, pc)
                ~f:(fun targets ->
                  Map.update (Option.value targets ~default:Int64.Map.empty)
                    next ~f:(fun n -> Option.value n ~default:0 + 1))
        | None -> ()
    done;
    Hashtbl.to_alist sites
    |> List.sort ~compare:(fun ((ta, a), _) ((tb, b), _) ->
        match Int.compare ta tb with 0 -> Int64.compare a b | c -> c)
    |> List.map ~f:(fun ((thread, site), targets) ->
        {
          thread;
          site;
          targets =
            Map.to_alist targets
            |> List.sort ~compare:(fun (a, n) (b, m) ->
                match Int.compare m n with 0 -> Int64.compare a b | c -> c);
        })

  (* the conditional branches of the trace, in their order, with the
     addresses, that they went to, and whether they were taken, i.e.,
     didn't fall through: the instructions, whose jumps on a condition
     leave them, as the jumps inside an instruction, e.g., over the body
     of a conditional instruction of ARM, aren't branches *)
  type branch = { site : int64; target : int64; taken : bool; thread : int }

  let branches ?thread ?last t =
    let pcs, _, modes, tids = window ?thread ?last t in
    let sizes = Int64.Table.create () in
    let branching thumb pc =
      let key = if thumb then Int64.(pc lor 1L) else pc in
      Hashtbl.find_or_add sizes key ~default:(fun () ->
          match lift ~thumb t.emu pc with
          | Some (size, blks) ->
              let inside = List.map blks ~f:Term.tid |> Tid.Hash_set.of_list in
              let leaves jmp =
                match Jmp.kind jmp with
                | Goto (Direct tid) -> not (Hash_set.mem inside tid)
                | Goto (Indirect _) | Call _ | Ret _ -> true
                | Int _ -> false
              in
              let conditional jmp =
                match Jmp.cond jmp with Int _ -> false | _ -> true
              in
              if
                List.exists blks ~f:(fun blk ->
                    Term.enum jmp_t blk
                    |> Seq.exists ~f:(fun jmp -> conditional jmp && leaves jmp))
              then Some size
              else None
          | None -> None)
    in
    let branches = ref [] in
    for i = 0 to Bigarray.Array1.dim pcs - 2 do
      let pc = Bigarray.Array1.unsafe_get pcs i in
      let thumb = Bigarray.Array1.unsafe_get modes i = 1 in
      let tid = Bigarray.Array1.unsafe_get tids i in
      if Int64.equal tid (Bigarray.Array1.unsafe_get tids (i + 1)) then
        match branching thumb pc with
        | Some size ->
            let target = Bigarray.Array1.unsafe_get pcs (i + 1) in
            branches :=
              {
                site = pc;
                target;
                taken = Int64.(target <> pc + of_int size);
                thread = Int64.to_int_exn tid;
              }
              :: !branches
        | None -> ()
    done;
    List.rev !branches
end

module Compare = struct
  include Bap_emu_compare

  let instructions ?thread trace =
    let pcs, _, _, tids = Trace.window ~records:false ?thread trace in
    List.init (Bigarray.Array1.dim pcs) ~f:(fun i ->
        Instruction
          {
            pc = Bigarray.Array1.unsafe_get pcs i;
            thread = Int64.to_int_exn (Bigarray.Array1.unsafe_get tids i);
          })

  let blocks ?thread trace =
    let pcs = Trace.pcs trace and tids = Trace.tids trace in
    let sizes = Trace.sizes trace in
    List.filter_map
      (List.init (Bigarray.Array1.dim pcs) ~f:Fn.id)
      ~f:(fun i ->
        let tid = Int64.to_int_exn (Bigarray.Array1.unsafe_get tids i) in
        Option.some_if
          (Option.for_all thread ~f:(fun selected -> tid = selected))
          (Block
             {
               pc = Bigarray.Array1.unsafe_get pcs i;
               size = Int32.to_int_trunc (Bigarray.Array1.unsafe_get sizes i);
               thread = tid;
             }))

  let branches ?thread trace =
    Trace.branches ?thread trace
    |> List.map ~f:(fun (branch : Trace.branch) ->
        Branch
          {
            site = branch.site;
            target = branch.target;
            taken = branch.taken;
            thread = branch.thread;
          })

  let calls ?thread trace =
    Trace.calls ?thread trace
    |> List.map ~f:(fun (call : Trace.call) ->
        Call { site = call.site; targets = call.targets; thread = call.thread })

  let captures ~thread capture =
    Trace.captured capture
    |> List.map ~f:(fun (site, values) -> Capture { site; values; thread })

  let writes ?thread trace =
    Trace.accesses trace
    |> List.filter ~f:(fun (access : Trace.access) ->
        access.write
        && Option.for_all thread ~f:(fun selected -> access.thread = selected))
    |> List.map ~f:(fun (access : Trace.access) ->
        Write
          {
            pc = access.pc;
            addr = access.addr;
            size = access.size;
            value = access.value;
            thread = access.thread;
          })
end

type 'a recorded = { result : ('a, string) result; trace : Trace.t }

(* [f] runs with a trace of its own, e.g., a call, so that the trace has
   the path of the callee only, also when it fails *)
let record ?size t f =
  let trace = Trace.start ?size t in
  let result =
    Exn.protect
      ~f:(fun () ->
        match f () with x -> Ok x | exception Failure msg -> Error msg)
      ~finally:(fun () -> Trace.stop trace)
  in
  { result; trace }

type location = Bap_emu_slice.location = Reg of string | Mem of int64 * int
type step = { index : int64; pc : int64; thread : int }

type empty_slice_reason =
  | No_dataflow
  | Unresolved_inputs
  | Outside_trace_writes
  | Instruction_decode

type slice = {
  steps : step list;
  live : location list;
  gaps : int64 list;
  complete : bool;
  reason : empty_slice_reason option;
  decode_failures : decode_failure list;
}

(* The registers, that an instruction writes, and, for the ones, that are
   needed, the registers, that it reads to compute them, and the loads,
   that they make, through its temporaries, as the defs of all its
   blocks run in order. The defs of the blocks, that the instruction may
   skip, e.g., of a compare and exchange, may keep the registers, so they
   stay live, and their values depend on the conditions of the jumps, as
   of a conditional move. The stores, that are recorded, did happen, so
   the conditions of the jumps, e.g., of a repeated move, are not in the
   slice of the data.

   The loads and the stores are numbered in the order, that they run in,
   so that they are the accesses of the record, e.g., of the registers,
   that a load or a store of multiple registers of ARM moves, if their
   sizes are the same. *)
module Insn = struct
  (* the variables of the values, and of the addresses, and the loads of
     the values, and of the addresses *)
  type use = {
    vars : Var.t list;
    addrs : Var.t list;
    loads : int list;
    aloads : int list;
  }

  type def = {
    lhs : Var.t;
    must : bool;  (** the def must happen *)
    use : use;
    stores : (int * use) list;  (** the stores of the memory, and their values *)
  }

  type t = {
    size : int;
    defs : def list;
    conds : use list;
    load_sizes : int list;  (** of the loads, in their order *)
    store_sizes : int list;
    written : String.Set.t;
  }

  let register v =
    (not (Var.is_virtual v))
    && match Var.typ v with Imm _ -> true | Mem _ | Unk -> false

  let name v = String.uppercase (Var.name v)

  (* the blocks, that are on each of the paths from the first block to the
     ones, that leave the instruction *)
  let must blks =
    let blks = Array.of_list blks in
    let index = Tid.Table.create () in
    Array.iteri blks ~f:(fun i b -> Hashtbl.set index ~key:(Term.tid b) ~data:i);
    let succs i =
      let jmps = Term.enum jmp_t blks.(i) |> Seq.to_list in
      let targets =
        List.filter_map jmps ~f:(fun j ->
            match Jmp.kind j with
            | Goto (Direct tid) -> Some (Hashtbl.find index tid)
            | _ -> Some None)
      in
      let falls =
        List.for_all jmps ~f:(fun j ->
            match Jmp.cond j with Int w -> Word.is_zero w | _ -> true)
      in
      (* the block, whose jumps are conditional, falls through *)
      if falls then None :: targets else targets
    in
    let leaves i ~avoid =
      let seen = Array.create ~len:(Array.length blks) false in
      let rec go i =
        (not (i = avoid || seen.(i)))
        && begin
          seen.(i) <- true;
          List.exists (succs i) ~f:(function None -> true | Some j -> go j)
        end
      in
      go i
    in
    Array.mapi blks ~f:(fun i _ ->
        i = 0 || Array.length blks = 1 || not (leaves 0 ~avoid:i))

  type acc = {
    mutable vars : Var.t list;
    mutable addrs : Var.t list;
    mutable loads : int list;
    mutable aloads : int list;
  }

  let fresh () = { vars = []; addrs = []; loads = []; aloads = [] }

  let use (a : acc) : use =
    { vars = a.vars; addrs = a.addrs; loads = a.loads; aloads = a.aloads }

  let of_blks size blks =
    let must = must blks in
    let load_sizes = ref [] and store_sizes = ref [] in
    let next sizes n =
      let id = List.length !sizes in
      sizes := n :: !sizes;
      id
    in
    (* the subexpressions run first, the address before the load or the
       store *)
    let rec go (acc : acc) ~addr stores e =
      let go' = go acc ~addr stores in
      match (e : exp) with
      | Var v -> (
          match Var.typ v with
          | Mem _ -> ()
          | _ ->
              if addr then acc.addrs <- v :: acc.addrs
              else acc.vars <- v :: acc.vars)
      | Load (m, a, _, sz) ->
          go' m;
          go acc ~addr:true stores a;
          let id = next load_sizes (Size.in_bytes sz) in
          if addr then acc.aloads <- id :: acc.aloads
          else acc.loads <- id :: acc.loads
      | Store (m, a, x, _, sz) ->
          go' m;
          let value = fresh () in
          go value ~addr:true stores a;
          go value ~addr:false stores x;
          let id = next store_sizes (Size.in_bytes sz) in
          stores := (id, use value) :: !stores;
          acc.vars <- value.vars @ acc.vars;
          acc.addrs <- value.addrs @ acc.addrs;
          acc.loads <- value.loads @ acc.loads;
          acc.aloads <- value.aloads @ acc.aloads
      | BinOp (_, x, y) | Concat (x, y) | Let (_, x, y) ->
          go' x;
          go' y
      | UnOp (_, x) | Cast (_, _, x) | Extract (_, _, x) -> go' x
      | Ite (c, x, y) ->
          go' c;
          go' x;
          go' y
      | Int _ | Unknown _ -> ()
    in
    let analyze e =
      let a = fresh () and stores = ref [] in
      go a ~addr:false stores e;
      (use a, List.rev !stores)
    in
    let defs = ref [] and conds = ref [] in
    List.iteri blks ~f:(fun i b ->
        Term.enum def_t b
        |> Seq.iter ~f:(fun d ->
            let use, stores = analyze (Def.rhs d) in
            defs := { lhs = Def.lhs d; must = must.(i); use; stores } :: !defs);
        Term.enum jmp_t b
        |> Seq.iter ~f:(fun j ->
            match Jmp.cond j with
            | Int _ -> ()
            | c -> conds := fst (analyze c) :: !conds));
    let defs = List.rev !defs in
    let written =
      List.filter_map defs ~f:(fun d ->
          Option.some_if (register d.lhs) (name d.lhs))
      |> String.Set.of_list
    in
    {
      size;
      defs;
      conds = List.rev !conds;
      load_sizes = List.rev !load_sizes;
      store_sizes = List.rev !store_sizes;
      written;
    }

  (* The registers, that compute the [needed] registers, and the stores,
     that [stored] tells, or all, if [stores] and it doesn't, and the
     loads, that they make, and whether they load, and whether the stores
     may not happen, as the instruction, which [rewrites] the bytes, that
     it reads, may write them back, e.g., a compare and exchange, that
     fails, which the semantics doesn't have. *)
  let inputs ~addresses insn ~needed ~stores ~stored ~rewrites =
    let live = Var.Hash_set.create () in
    let loads = Int.Hash_set.create () in
    let take (u : use) =
      List.iter u.vars ~f:(Hash_set.add live);
      List.iter u.loads ~f:(Hash_set.add loads);
      if addresses then begin
        List.iter u.addrs ~f:(Hash_set.add live);
        List.iter u.aloads ~f:(Hash_set.add loads)
      end
    in
    (* the conditions are taken at the end, before the temporaries,
       that compute them, if a def, that is needed, may not happen *)
    let walk ~conds =
      Hash_set.clear live;
      Hash_set.clear loads;
      List.iter insn.defs ~f:(fun d ->
          if register d.lhs && Set.mem needed (name d.lhs) then
            Hash_set.add live d.lhs);
      if conds then List.iter insn.conds ~f:take;
      List.fold (List.rev insn.defs) ~init:false ~f:(fun skipped d ->
          match Var.typ d.lhs with
          | Mem _ ->
              let taken =
                match stored with
                | Some stored ->
                    List.fold d.stores ~init:false ~f:(fun taken (id, u) ->
                        if stored id then (
                          take u;
                          true)
                        else taken)
                | None ->
                    if stores then take d.use;
                    stores
              in
              skipped || (taken && rewrites && not d.must)
          | _ ->
              if Hash_set.mem live d.lhs then begin
                if d.must then Hash_set.remove live d.lhs;
                take d.use;
                skipped || not d.must
              end
              else skipped)
    in
    let skipped = walk ~conds:false in
    if skipped then ignore (walk ~conds:true : bool);
    let regs =
      Hash_set.to_list live
      |> List.filter_map ~f:(fun v -> Option.some_if (register v) (name v))
    in
    (regs, Hash_set.to_list loads, skipped && stores && rewrites)
end

(* the bytes of the locations, coalesced *)
let ranges bytes =
  List.sort (Hash_set.to_list bytes) ~compare:Int64.compare
  |> List.fold ~init:[] ~f:(fun acc a ->
      match acc with
      | Mem (b, n) :: rest when Int64.(b + of_int n = a) ->
          Mem (b, n + 1) :: rest
      | _ -> Mem (a, 1) :: acc)
  |> List.rev

(* The slice goes backward from the last recorded instruction, whose
   defs of the live locations make it a step, which kills them, and
   makes its inputs live, the registers, that compute them, and the
   bytes, that it read, if they load, as the trace has their addresses.
   The instructions of a trace of blocks are of their blocks, and their
   accesses are found by their program counters. The instructions are
   lifted once, from the bytes, that they have now, outside of the
   machine, as in the hooks, or from the executed history, if their
   current bytes don't decode and [executed_bytes] is set. *)
let slice ?(addresses = false) ?(executed_bytes = false) ?window ?thread
    (tr : Trace.t) criterion =
  let t = tr.emu in
  let w = Trace.expanded_window ~executed_bytes ?thread ?last:window tr in
  let pcs, records, modes, tids = (w.pcs, w.records, w.modes, w.tids) in
  let n = Bigarray.Array1.dim pcs in
  let decode_failures = Hashtbl.Poly.create () in
  List.iter w.failures ~f:(fun f ->
      Hashtbl.set decode_failures ~key:(f.index, f.pc) ~data:f);
  let blocks = Trace.blocks tr in
  let rows = Engine.Trace.accesses tr.trace in
  let rows_n = Bigarray.Array2.dim1 rows in
  let first_record =
    if n = 0 then Trace.count tr else Bigarray.Array1.get records 0
  in
  (* the records before the oldest kept access, whose accesses the ring
     has lost, aren't in the window, as the record of the oldest one, that
     may have lost its first accesses *)
  let covered =
    if
      (not tr.memory)
      || Int64.(Engine.Trace.accesses_count tr.trace = of_int rows_n)
    then first_record
    else if rows_n = 0 then Trace.count tr
    else Int64.(max first_record ((Trace.access rows 0).insn + 1L))
  in
  let live_regs = String.Hash_set.create () in
  let live_mem = Int64.Hash_set.create () in
  List.iter criterion ~f:(function
    | Reg r -> Hash_set.add live_regs (String.uppercase r)
    | Mem (a, size) ->
        for i = 0 to size - 1 do
          Hash_set.add live_mem Int64.(a + of_int i)
        done);
  (* the loads, whose bytes the trace doesn't have *)
  let untracked = ref false in
  (* the records, before which the registers, the bit 62, or the memory,
     the bit 63, were written outside of the trace, with the written
     bytes, if they are known, and the ones, whose instructions, by the
     records and the program counters, a hook wrote them before, the bit
     61, see [Engine.Trace.bounds] *)
  let bounds = Int64.Table.create () and inside = Hashtbl.Poly.create () in
  let marks = Engine.Trace.bounds tr.trace
  and written = Engine.Trace.ranges tr.trace in
  let pos = ref 0 in
  for i = 0 to (Bigarray.Array1.dim marks / 4) - 1 do
    let b = Bigarray.Array1.get marks (4 * i) in
    let record = Int64.(b land 0x1FFF_FFFF_FFFF_FFFFL) in
    let regs = Int64.(b land 0x4000_0000_0000_0000L <> 0L) in
    let mem = Int64.(b < 0L) in
    let n = Int64.to_int_exn (Bigarray.Array1.get marks ((4 * i) + 2)) in
    let ranges =
      if n < 0 then None
      else
        Some
          (List.init n ~f:(fun j ->
               let k = 2 * (!pos + j) in
               Bigarray.Array1.(get written k, get written (k + 1))))
    in
    pos := !pos + Int.max n 0;
    let tid = Int64.to_int_exn (Bigarray.Array1.get marks ((4 * i) + 3)) in
    let merge = function
      | None -> [ (tid, (regs, mem, ranges)) ]
      | Some marks -> (tid, (regs, mem, ranges)) :: marks
    in
    if Int64.(b land 0x2000_0000_0000_0000L = 0L) then
      Hashtbl.update bounds record ~f:(fun old ->
          Option.value_map old
            ~default:[ (tid, (regs, mem, ranges)) ]
            ~f:(fun marks -> (tid, (regs, mem, ranges)) :: marks))
    else
      let pc = Bigarray.Array1.get marks ((4 * i) + 1) in
      Hashtbl.update inside (record, pc) ~f:merge
  done;
  let gaps = ref [] in
  (* the live bytes, that were written outside, come from there, and
     aren't live before, unless the written ones are unknown *)
  let gap record tid (regs, mem, ranges) =
    let outside =
      match ranges with
      | Some ranges when mem ->
          Hash_set.filter live_mem ~f:(fun a ->
              List.exists ranges ~f:(fun (b, n) -> Int64.(a >= b && a - b < n)))
      | _ -> Int64.Hash_set.create ()
    in
    let our_regs = Option.for_all thread ~f:(Int.equal tid) in
    if
      (our_regs && regs && not (Hash_set.is_empty live_regs))
      || mem
         &&
         if Option.is_some ranges then not (Hash_set.is_empty outside)
         else not (Hash_set.is_empty live_mem)
    then gaps := record :: !gaps;
    Hash_set.iter outside ~f:(Hash_set.remove live_mem)
  in
  (* the values of the live locations may come from outside of the trace,
     before the instruction, that a hook wrote them before, or before the
     first instruction of a record, that follows a boundary *)
  let crossed k =
    let record = Bigarray.Array1.get records k in
    if not (Hashtbl.is_empty inside) then
      List.iter
        (Option.value
           (Hashtbl.find inside (record, Bigarray.Array1.get pcs k))
           ~default:[])
        ~f:(fun (tid, marks) -> gap record tid marks);
    if k = 0 || not (Int64.equal (Bigarray.Array1.get records (k - 1)) record)
    then
      List.iter
        (Option.value (Hashtbl.find bounds record) ~default:[])
        ~f:(fun (tid, marks) -> gap record tid marks)
  in
  (* the bytes of the code, that the later writes changed, as they were
     at the instruction, which the walk is at, i.e., the bytes, that the
     earliest of the writes, that it saw, overwrote, or [None], if they
     are unknown, e.g., of a wide write *)
  let earlier = Int64.Table.create () in
  let executable = Int64.Table.create () in
  let is_code addr =
    let page = X.page_of addr in
    Hashtbl.find_or_add executable page ~default:(fun () ->
        match Hashtbl.find (engine t).pages page with
        | Some { perm; _ } -> Engine.Perm.(mem perm exec)
        | None -> false)
  in
  let overwrote (a : Trace.access) =
    if a.write then
      for i = 0 to a.size - 1 do
        let addr = Int64.(a.addr + of_int i) in
        if is_code addr then
          Hashtbl.set earlier ~key:addr
            ~data:
              (Option.some_if (a.size <= 8)
                 (Char.of_int_exn
                    Int64.(
                      to_int_exn
                        (shift_right_logical a.old Int.(8 * i) land 0xFFL))))
      done
  in
  let lifted = Int64.Table.create () in
  (* the instruction, in its mode, as it was, if the program patched it
     later, and its bytes are known, or else as it is now *)
  let insn ~thumb pc =
    let now () =
      let key = if thumb then Int64.(pc lor 1L) else pc in
      Hashtbl.find_or_add lifted key ~default:(fun () ->
          Option.map (lift_with_history ~executed_bytes ~thumb t pc)
            ~f:(fun (size, blks) -> Insn.of_blks size blks))
    in
    if Hashtbl.is_empty earlier then now ()
    else
      let bytes = code_bytes t pc in
      let changed = ref false and known = ref true in
      let old =
        String.mapi bytes ~f:(fun i c ->
            match Hashtbl.find earlier Int64.(pc + of_int i) with
            | Some (Some c') ->
                if Char.(c <> c') then changed := true;
                c'
            | Some None ->
                known := false;
                c
            | None -> c)
      in
      if !changed && !known then
        Option.map (lift_with_history ~executed_bytes ~thumb ~bytes:old t pc)
          ~f:(fun (size, blks) -> Insn.of_blks size blks)
      else now ()
  in
  (* The instructions of an IT block of Thumb have the conditions, that
     the decoder of LLVM keeps, as it decodes the IT instruction, and the
     next ones, and their lifts are kept, so the block is lifted in its
     order, from the IT instruction, that is in the 4 records before the
     instruction, before the walk, which goes backward, lifts one of
     them. The IT block before the window isn't known. *)
  let it_length = Int64.Table.create () in
  let it_block pc =
    Hashtbl.find_or_add it_length pc ~default:(fun () ->
        match code_bytes t pc with
        | b when String.length b >= 2 ->
            let h = Char.to_int b.[0] lor (Char.to_int b.[1] lsl 8) in
            let mask = h land 0xF in
            if h land 0xFF00 = 0xBF00 && mask <> 0 then 4 - Int.ctz mask else 0
        | _ -> 0)
  in
  let grouped = Int64.Hash_set.create () in
  let is_thumb k =
    k >= 0 && k < Bigarray.Array1.dim modes && Bigarray.Array1.get modes k = 1
  in
  let in_order k =
    Sequence.range ~stop:`inclusive (Int.max 0 (k - 4)) k
    |> Sequence.find ~f:(fun j ->
        is_thumb j && j < k && k - j <= it_block (Bigarray.Array1.get pcs j))
    |> Option.iter ~f:(fun j ->
        let it = Bigarray.Array1.get pcs j in
        if not (Hash_set.mem grouped it) then begin
          Hash_set.add grouped it;
          (* by the addresses, as the instructions, whose conditions
             fail, have no records *)
          let rec lift pc i =
            if i >= 0 then
              match insn ~thumb:true pc with
              | Some { size; _ } when size > 0 ->
                  lift Int64.(pc + of_int size) (i - 1)
              | _ -> ()
          in
          lift it (it_block it)
        end)
  in
  (* the access is of the instruction at [k], of a later one, whose
     access is skipped, or of an earlier one, as the instructions of a
     block of a trace of blocks have increasing addresses *)
  let order k (a : Trace.access) =
    let record = Bigarray.Array1.get records k in
    if Int64.(a.insn > record) then `Later
    else if Int64.(a.insn < record) then `Earlier
    else if not blocks then `Ours
    else
      let pc = Bigarray.Array1.get pcs k in
      if Int64.(a.pc > pc) then `Later
      else if Int64.(a.pc < pc) then `Earlier
      else `Ours
  in
  let before_next k (a : Trace.access) =
    k + 1 < n
    && match order (k + 1) a with `Earlier -> true | `Ours | `Later -> false
  in
  let rec loop k row steps =
    if
      k < 0
      || Int64.(Bigarray.Array1.get records k < covered)
      || (Hash_set.is_empty live_regs && Hash_set.is_empty live_mem)
    then steps
    else
      let record = Bigarray.Array1.get records k in
      (* the accesses of the instruction, which are before [row] *)
      let rec accesses row reads writes =
        if row < 0 then row
        else
          let a = Trace.access rows row in
          match order k a with
          | `Later ->
              overwrote a;
              if
                a.write && before_next k a
                && Option.exists thread ~f:(fun tid -> a.thread <> tid)
              then
                gap a.insn a.thread
                  (false, true, Some [ (a.addr, Int64.of_int a.size) ]);
              accesses (row - 1) reads writes
          | `Ours ->
              overwrote a;
              (if a.write then writes else reads)
              := a :: !(if a.write then writes else reads);
              accesses (row - 1) reads writes
          | `Earlier -> row
      in
      let reads = ref [] and writes = ref [] in
      let row = accesses row reads writes in
      (* the accesses, in their order *)
      let bytes_of (a : Trace.access) =
        List.init a.size ~f:(fun i -> Int64.(a.addr + of_int i))
      in
      let read_bytes = List.concat_map !reads ~f:bytes_of
      and write_bytes = List.concat_map !writes ~f:bytes_of in
      let pc = Bigarray.Array1.get pcs k in
      let stores = List.exists write_bytes ~f:(Hash_set.mem live_mem) in
      let thumb = is_thumb k in
      if thumb then in_order k;
      match insn ~thumb pc with
      | None ->
          Hashtbl.set decode_failures ~key:(record, pc)
            ~data:
              {
                index = record;
                pc;
                block = Array.unsafe_get w.sources k;
                thread = Int64.to_int_exn (Bigarray.Array1.get tids k);
              };
          crossed k;
          loop (k - 1) row steps
      | Some i ->
          let needed = Set.filter i.written ~f:(Hash_set.mem live_regs) in
          if Set.is_empty needed && not stores then begin
            crossed k;
            loop (k - 1) row steps
          end
          else begin
            let rewrites =
              List.exists write_bytes
                ~f:(List.mem read_bytes ~equal:Int64.equal)
            in
            (* the accesses of the loads and the stores, by their numbers,
               if they are the same *)
            let matched accesses sizes =
              let accesses = Array.of_list accesses in
              Option.some_if
                (List.equal Int.equal sizes
                   (Array.to_list accesses
                   |> List.map ~f:(fun (a : Trace.access) -> a.size)))
                (fun id -> bytes_of accesses.(id))
            in
            let loaded = matched !reads i.load_sizes in
            let stored =
              Option.map (matched !writes i.store_sizes) ~f:(fun bytes id ->
                  List.exists (bytes id) ~f:(Hash_set.mem live_mem))
            in
            let regs, loads, kept =
              Insn.inputs ~addresses i ~needed ~stores ~stored ~rewrites
            in
            Set.iter needed ~f:(Hash_set.remove live_regs);
            if not kept then List.iter write_bytes ~f:(Hash_set.remove live_mem);
            List.iter regs ~f:(Hash_set.add live_regs);
            if not (List.is_empty loads) then
              if tr.memory then
                match loaded with
                | Some bytes ->
                    List.iter loads ~f:(fun id ->
                        List.iter (bytes id) ~f:(Hash_set.add live_mem))
                | None -> List.iter read_bytes ~f:(Hash_set.add live_mem)
              else untracked := true;
            crossed k;
            let thread = Int64.to_int_exn (Bigarray.Array1.get tids k) in
            loop (k - 1) row ({ index = record; pc; thread } :: steps)
          end
  in
  let steps = loop (n - 1) (rows_n - 1) [] in
  let live =
    (Hash_set.to_list live_regs
    |> List.sort ~compare:String.compare
    |> List.map ~f:(fun r -> Reg r))
    @ ranges live_mem
  in
  let gaps = List.rev !gaps in
  let decode_failures =
    List.init n ~f:Fn.id
    |> List.filter_map ~f:(fun k ->
        let key = (Bigarray.Array1.get records k, Bigarray.Array1.get pcs k) in
        Hashtbl.find decode_failures key)
  in
  let reason =
    if not (List.is_empty steps) then None
    else if not (List.is_empty decode_failures) then Some Instruction_decode
    else if not (List.is_empty gaps) then Some Outside_trace_writes
    else if not (List.is_empty live) then Some Unresolved_inputs
    else Some No_dataflow
  in
  {
    steps;
    live;
    gaps;
    complete = List.is_empty live && List.is_empty gaps && not !untracked;
    reason;
    decode_failures;
  }

let observe ~deferred t f = if deferred then defer t (fun t -> f t) else f t

let on_code ?first ?last ?(deferred = false) t f =
  hook t (fun e ->
      let fresh = instructions t in
      [
        Engine.on_code ?first ?last e.engine (fun addr _ ->
            if fresh addr then observe ~deferred t (fun t -> f t addr));
      ])

let on_sites ?(deferred = false) t sites f =
  sites_hook t sites (fun addr -> observe ~deferred t (fun t -> f t addr))

let on_read ?first ?last ?(deferred = false) t f =
  hook t (fun e ->
      [
        Engine.on_mem ?first ?last e.engine [ `read ] (fun _ addr size _ ->
            observe ~deferred t (fun t -> f t addr size));
      ])

(* the bytes, that Primus, or a native function, stored from [addr], in
   [first] to [last], go to the hook in the pieces of at most 8 bytes,
   whose values are of the endianness of the target, as Unicorn tells
   them *)
let stored t ?first ?last f addr data =
  let module Theory = Bap_core_theory.Theory in
  let big = Theory.Endianness.(equal eb) (Theory.Target.endianness t.target) in
  let inside x =
    Option.for_all first ~f:(fun a -> Stdlib.Int64.unsigned_compare a x <= 0)
    && Option.for_all last ~f:(fun b -> Stdlib.Int64.unsigned_compare x b <= 0)
  in
  let value piece =
    let bytes = String.to_list piece in
    let bytes = if big then bytes else List.rev bytes in
    List.fold bytes ~init:0L ~f:(fun x c ->
        Int64.(shift_left x 8 lor of_int (Char.to_int c)))
  in
  let n = String.length data in
  let rec go i =
    if i < n then (
      if not (inside Int64.(addr + of_int i)) then go (i + 1)
      else
        let rec stop j =
          if j < n && j - i < 8 && inside Int64.(addr + of_int j) then
            stop (j + 1)
          else j
        in
        let j = stop i in
        let piece = String.sub data ~pos:i ~len:(j - i) in
        f t Int64.(addr + of_int i) (j - i) (value piece);
        go j)
  in
  go 0

type write_handler = {
  subscription : write_subscription;
  mutable last_attempt :
    (int64 * int * int64 option * (int64 * int * int64) list) option;
  mutable active_attempt : (int64 * int * int64 option) option;
  mutable events : (int64 * int * int64) list;
  mutable replay : (int64 * int * int64) list;
}

let invoke_write t handler addr size value =
  observe ~deferred:handler.subscription.deferred t (fun t ->
      t.write_callbacks <- t.write_callbacks + 1;
      let started = Caml_unix.gettimeofday () in
      Exn.protect
        ~f:(fun () -> handler.subscription.callback t addr size value)
        ~finally:(fun () ->
          t.write_seconds <-
            t.write_seconds +. (Caml_unix.gettimeofday () -. started)))

let deliver_write t handler addr size value =
  let pc = code_of t (pc t) in
  let start = t.session.starts in
  let attempt =
    match t.session.active with
    | Some e -> Engine.attempt e.engine
    | None -> None
  in
  let fresh =
    match handler.active_attempt with
    | Some (previous_pc, previous_start, previous_attempt) -> (
        (not (Int64.equal previous_pc pc))
        ||
        match (attempt, previous_attempt) with
        | Some current, Some previous -> not (Int64.equal current previous)
        | _ -> previous_start <> start)
    | None -> true
  in
  if fresh then begin
    handler.active_attempt <- Some (pc, start, attempt);
    handler.events <- [];
    handler.replay <-
      (match handler.last_attempt with
      | Some (previous_pc, previous_start, previous_attempt, previous_events)
        when Int64.equal previous_pc pc
             && (match (attempt, previous_attempt) with
               | Some current, Some previous -> Int64.(current > previous)
               | _ -> previous_start < start)
             && (previous_start = start
                || Option.equal Int64.equal t.session.restarted_at (Some pc)) ->
          List.rev previous_events
      | _ -> [])
  end;
  let event = (addr, size, value) in
  handler.events <- event :: handler.events;
  handler.last_attempt <- Some (pc, start, attempt, handler.events);
  match handler.replay with
  | expected :: rest when Poly.equal expected event -> handler.replay <- rest
  | _ ->
      handler.replay <- [];
      invoke_write t handler addr size value

let on_writes t subscriptions =
  let handlers =
    List.map subscriptions ~f:(fun subscription ->
        {
          subscription;
          last_attempt = None;
          active_attempt = None;
          events = [];
          replay = [];
        })
  in
  let groups =
    List.fold handlers ~init:[] ~f:(fun groups handler ->
        let range = (handler.subscription.first, handler.subscription.last) in
        match groups with
        | (other, handlers) :: rest when Poly.equal range other ->
            (range, handler :: handlers) :: rest
        | _ -> (range, [ handler ]) :: groups)
  in
  List.iter groups ~f:(fun ((first, last), handlers) ->
      hook t (fun e ->
          [
            Engine.on_mem ?first ?last e.engine [ `write ]
              (fun _ addr size value ->
                t.write_dispatches <- t.write_dispatches + 1;
                List.iter (List.rev handlers) ~f:(fun handler ->
                    deliver_write t handler addr size value));
          ]));
  List.iter handlers ~f:(fun handler ->
      if handler.subscription.primus then begin
        let h =
          stored t ?first:handler.subscription.first
            ?last:handler.subscription.last (fun _ addr size value ->
              invoke_write t handler addr size value)
        in
        t.session.store_hooks <- h :: t.session.store_hooks;
        scope t (fun () ->
            t.session.store_hooks <-
              List.filter t.session.store_hooks ~f:(fun g ->
                  not (phys_equal g h)))
      end)

let on_write ?first ?last ?(primus = false) ?(deferred = false) t f =
  on_writes t [ { first; last; primus; deferred; callback = f } ]

let write_profile t =
  {
    dispatches = t.write_dispatches;
    callbacks = t.write_callbacks;
    seconds = t.write_seconds;
  }

let add_service t name =
  Hashtbl.update t.services name ~f:(function
    | None -> 1
    | Some count -> count + 1)

let remove_service t name =
  Hashtbl.change t.services name ~f:(function
    | None | Some 1 -> None
    | Some count -> Some (count - 1))

let on_import t ~site ~name f =
  add_service t name;
  let hook () =
    t.call <- Some name;
    Exn.protect
      ~f:(fun () ->
        match f t with
        | Default -> ()
        | Return x ->
            record_event t "relocation" (sprintf "%Lx:%s:0x%Lx" site name x);
            let e = engine t in
            let ret = X.import_return e name x in
            e.reason <- Some (X.Jump ret);
            Engine.stop e.engine)
      ~finally:(fun () -> t.call <- None)
  in
  sites_hook t [ site ] (fun _ -> hook ());
  scope t (fun () -> remove_service t name)

let relocation_journal t =
  Queue.to_list t.session.journal
  |> List.map ~f:(fun (event : X.journal_event) ->
      { kind = event.kind; detail = event.detail })
  |> List.filter ~f:(fun event -> String.equal event.kind "relocation")

(* the functions of the program, which no stub replaces, are hooked at
   their addresses, once, by the name, that the address has, when it is
   called, see [add_symbol], and the others stop Unicorn, see
   [X.call_returns] *)
let hook_calls t addr =
  if not (Hash_set.mem t.hooked_calls addr) then begin
    Hash_set.add t.hooked_calls addr;
    installed t (fun e ->
        (* the call is seen once, as the first instruction of the
           function runs again, when Unicorn starts at it again, after
           the hook saw it, and Unicorn stopped there, e.g., as the hook
           stops it *)
        let fresh = instructions t in
        ignore
          (Engine.on_code e.engine ~first:addr ~last:addr (fun addr _ ->
               let s = t.session in
               if fresh addr && not (Hash_set.mem e.foreign addr) then
                 match
                   Option.bind (Hashtbl.find s.names addr) ~f:(X.call_returns e)
                 with
                 | Some ret ->
                     e.reason <- Some (X.Jump ret);
                     Engine.stop e.engine
                 | None -> ())))
  end

(* the hooks of the system calls, which the ABI of Linux of the target
   tells, see [X.Make.Threads.hooked] *)
let action_result = function
  | Default -> "default"
  | Return value -> sprintf "0x%Lx" value

let on_syscall t f =
  let h number args =
    let result = f t number args in
    record_event t "syscall" (sprintf "%Ld:%s" number (action_result result));
    match result with Default -> X.Default | Return x -> X.Return x
  in
  t.session.syscall_hooks <- h :: t.session.syscall_hooks;
  scope t (fun () ->
      t.session.syscall_hooks <-
        List.filter t.session.syscall_hooks ~f:(fun g -> not (phys_equal g h)))

let on_call t name f =
  add_service t name;
  let hook () =
    t.call <- Some name;
    Exn.protect
      ~f:(fun () ->
        let result = f t in
        record_event t "import" (sprintf "%s:%s" name (action_result result));
        match result with Default -> X.Default | Return x -> X.Return x)
      ~finally:(fun () -> t.call <- None)
  in
  Hashtbl.add_multi t.session.call_hooks ~key:name ~data:hook;
  (* the addresses stay hooked, and their hooks see no hooks of the
     calls by the name, see [X.call_returns] *)
  scope t (fun () ->
      Hashtbl.change t.session.call_hooks name ~f:(function
        | None -> None
        | Some hooks -> (
            match List.filter hooks ~f:(fun g -> not (phys_equal g hook)) with
            | [] -> None
            | hooks -> Some hooks));
      remove_service t name);
  Hashtbl.iteri t.session.names ~f:(fun ~key:addr ~data ->
      if String.equal data name then hook_calls t addr)

(* the name goes to the checkpoints, and replaces the name, that the
   address had, e.g., of the program *)
let add_symbol t name addr =
  Hashtbl.set t.session.symbols ~key:addr ~data:name;
  Hashtbl.set t.session.names ~key:addr ~data:name;
  if Hashtbl.mem t.session.call_hooks name then hook_calls t addr

let register_stub t ~name ~address =
  add_symbol t name address;
  hook t (fun e ->
      let fresh = instructions t in
      [
        Engine.on_code e.engine ~first:address ~last:address (fun _ _ ->
            if fresh address && not (Hashtbl.mem t.services name) then
              warning
                "Bap_emu: synthetic stub %s at %Lx has no registered service"
                name address);
      ])

let symbols t =
  Hashtbl.to_alist t.session.names
  |> List.sort ~compare:(fun (a, _) (b, _) -> Int64.compare a b)
  |> List.map ~f:(fun (addr, name) -> (name, addr))

module Xrefs = Bap_emu_xrefs
module Static = Bap_emu_slice
module AArch64 = Bap_emu_aarch64

module Jni = struct
  type emulator = t

  include Bap_emu_jni

  include Bap_emu_jni.Make (struct
    type t = emulator

    let read = read
    let write = write
    let reg = reg
    let set_reg = set_reg
    let set_pc = set_pc
    let event t detail = record_event t "jni" detail
  end)

  let bind_checkpoint ?(package = "user") ?(version = 1) ?(required = true)
      models jni =
    Checkpoint.register ~package ~version ~required models "jni"
      ~save:(fun () -> Some (export_state jni))
      ~restore:(import_state jni)
end

module Android = struct
  include Bap_emu_android

  let bind_checkpoint ?(package = "user") ?(version = 1) ?(required = true)
      models android =
    Checkpoint.register ~package ~version ~required models "android"
      ~save:(fun () -> Some (export_state android))
      ~restore:(import_state android)
end

(* the projects of the memory, each in a unit of its own, as the memory
   changes between them *)
let projects = ref 0

(* the digest of the code, that a project of the memory is made of *)
let project_digest = Bap_emu_xrefs.project_digest

(* the readable regions, with their bytes, from Primus, which has them
   all, as Unicorn has only the pages, that the code touched, without the
   bytes, that were never stored, e.g., of the stack, which are zero *)
let dump ?(only = fun _ -> true) t =
  List.filter_map (regions t) ~f:(fun r ->
      let len = Int64.(to_int_exn (r.upper - r.lower + 1L)) in
      if r.readable && only r then begin
        resume t (X.Dump (r.lower, len));
        Some (r, t.session.dumped)
      end
      else None)

let region_name (r : region) =
  sprintf "live:%s%s%s" "r"
    (if r.writable then "w" else "-")
    (if r.executable then "x" else "-")

(* the names of the script, and of the caller *)
let names t symbols =
  Hashtbl.to_alist t.session.symbols
  |> List.map ~f:(fun (addr, name) -> (name, addr))
  |> fun names -> names @ symbols

let selected ?regions (r : region) =
  r.executable
  && Option.value_map regions ~default:true ~f:(fun select -> select r)

let digest ?regions t ~symbols ~roots dumped =
  let module Theory = Bap_core_theory.Theory in
  let buf = Buffer.create 4096 in
  Buffer.add_string buf (Theory.Target.to_string t.target);
  List.iter dumped ~f:(fun ((r : region), bytes) ->
      if r.executable then begin
        Buffer.add_string buf (sprintf "%Lx-%Lx\n" r.lower r.upper);
        Buffer.add_string buf bytes
      end);
  Option.iter regions ~f:(fun _ ->
      Buffer.add_string buf "scoped-regions\n";
      List.filter dumped ~f:(fun (r, _) -> selected ?regions r)
      |> List.map ~f:(fun ((r : region), _) -> (r.lower, r.upper))
      |> List.sort ~compare:(fun (a, b) (c, d) ->
          match Int64.compare a c with 0 -> Int64.compare b d | order -> order)
      |> List.iter ~f:(fun (lower, upper) ->
          Buffer.add_string buf (sprintf "%Lx-%Lx\n" lower upper)));
  List.iter (names t symbols) ~f:(fun (name, addr) ->
      Buffer.add_string buf (sprintf "%s@%Lx\n" name addr));
  List.iter (List.dedup_and_sort roots ~compare:Int64.compare) ~f:(fun addr ->
      Buffer.add_string buf (sprintf "@%Lx\n" addr));
  Md5.to_hex (Md5.digest_string (Buffer.contents buf))

let code_digest ?regions ?(symbols = []) ?(roots = []) t =
  if not (paused t) then not_paused ~fn:"code_digest" t;
  digest ?regions t ~symbols ~roots (dump ~only:(fun r -> r.executable) t)

let endian target =
  let module Theory = Bap_core_theory.Theory in
  if Theory.Endianness.(Theory.Target.endianness target = le) then LittleEndian
  else BigEndian

(* The saved projects of the memory: the program, the memory, the
   target, and the digest, as the files, from which they are loaded,
   without the disassembly, which they keep. *)
module Saved = struct
  (* the bytes of a region, whose runs of zeros, e.g., of the stack, that
     the program never stored, are their lengths *)
  type piece = Bytes of string | Zeros of int [@@deriving bin_io]

  type region = { lower : int64; name : string; pieces : piece list }
  [@@deriving bin_io]

  let pieces bytes =
    let n = String.length bytes in
    let rec go i acc =
      if i >= n then List.rev acc
      else
        let j = ref i in
        while !j < n && Char.equal bytes.[!j] '\000' do
          incr j
        done;
        if !j - i >= 64 then go !j (Zeros (!j - i) :: acc)
        else begin
          (* the bytes up to the next long run of zeros *)
          let k = ref !j in
          let zeros = ref 0 in
          while !k < n && !zeros < 64 do
            if Char.equal bytes.[!k] '\000' then incr zeros else zeros := 0;
            incr k
          done;
          let stop = if !zeros >= 64 then !k - !zeros else !k in
          go stop (Bytes (String.sub bytes ~pos:i ~len:(stop - i)) :: acc)
        end
    in
    go 0 []

  let bytes pieces =
    String.concat
      (List.map pieces ~f:(function
        | Bytes s -> s
        | Zeros n -> String.make n '\000'))

  type t = {
    target : string;
    filename : string;
    digest : string;
    program : string;
    state : Project.state;
    spec : Ogre.Doc.t;
    code : region list;
    data : region list;
  }
  [@@deriving bin_io]

  let magic = "bap-emu-project 3\n"
end

(* the program, with the addresses of its terms only, as the other
   attributes, e.g., the instructions, that each term carries, take
   most of the space, and the analyses of the saved projects don't read
   them *)
let slim prog =
  let keep t =
    Term.with_attrs t
      (match Term.get_attr t address with
      | Some a -> Dict.set Dict.empty address a
      | None -> Dict.empty)
  in
  Term.map sub_t prog ~f:(fun sub ->
      keep sub
      |> Term.map blk_t ~f:(fun blk ->
          keep blk |> Term.map def_t ~f:keep |> Term.map jmp_t ~f:keep
          |> Term.map phi_t ~f:keep))

let save_project proj file =
  let module Theory = Bap_core_theory.Theory in
  let regions memmap =
    Memmap.to_sequence memmap
    |> Seq.map ~f:(fun (mem, v) ->
        {
          Saved.lower = Bitvec.to_int64 (Word.to_bitvec (Memory.min_addr mem));
          name = Option.value (Value.get Image.section v) ~default:"";
          pieces = Saved.pieces (Memory.to_buffer mem |> Bigsubstring.to_string);
        })
    |> Seq.to_list
  in
  let code, data =
    Memmap.to_sequence (Project.memory proj)
    |> Seq.to_list
    |> List.partition_tf ~f:(fun (_, v) ->
        Option.exists (Value.get Image.section v) ~f:(fun name ->
            String.is_suffix name ~suffix:"x"))
  in
  let memmap =
    List.fold ~init:Memmap.empty ~f:(fun m (mem, v) -> Memmap.add m mem v)
  in
  let saved =
    {
      Saved.target = Theory.Target.to_string (Project.target proj);
      filename = Option.value (Project.get proj filename) ~default:"a.out";
      digest = Option.value (project_digest proj) ~default:"";
      program = Binable.to_string (module Program) (slim (Project.program proj));
      state = Project.state proj;
      spec = Project.specification proj;
      code = regions (memmap code);
      data = regions (memmap data);
    }
  in
  Out_channel.write_all file
    ~data:(Saved.magic ^ Binable.to_string (module Saved) saved)

let load_project file =
  let module Theory = Bap_core_theory.Theory in
  let data =
    try In_channel.read_all file
    with Sys_error msg -> failwithf "Bap_emu.load_project: %s" msg ()
  in
  match String.chop_prefix data ~prefix:Saved.magic with
  | None -> failwithf "Bap_emu.load_project: %s is not a saved project" file ()
  | Some data -> (
      let saved =
        try Binable.of_string (module Saved) data
        with exn ->
          failwithf "Bap_emu.load_project: %s is broken: %s" file
            (Exn.to_string exn) ()
      in
      let target = Theory.Target.read saved.target in
      let width = Theory.Target.code_addr_size target in
      let endian = endian target in
      let memmap regions =
        List.fold regions ~init:Memmap.empty ~f:(fun m (r : Saved.region) ->
            let mem =
              Memory.create endian
                (Addr.of_int64 ~width r.lower)
                (Bigstring.of_string (Saved.bytes r.pieces))
              |> Or_error.ok_exn
            in
            Memmap.add m mem (Value.create Image.section r.name))
      in
      let program = Binable.of_string (module Program) saved.program in
      match
        Project.create ~package:saved.filename ~state:saved.state ~program
          (Project.Input.custom ~filename:saved.filename ~spec:saved.spec
             ~code:(memmap saved.code) ~data:(memmap saved.data) target)
      with
      | Ok proj -> Bap_emu_xrefs.set_project_digest proj saved.digest
      | Error err ->
          failwithf "Bap_emu.load_project: %s" (Error.to_string_hum err) ())

let project ?regions ?(symbols = []) ?(roots = []) ?cache t =
  if not (paused t) then not_paused ~fn:"project" t;
  let target = t.target in
  let module Theory = Bap_core_theory.Theory in
  let width = Theory.Target.code_addr_size target in
  let endian = endian target in
  let dumped = dump t in
  let digest = digest ?regions t ~symbols ~roots dumped in
  let build () =
    let code, data =
      List.fold dumped ~init:(Memmap.empty, Memmap.empty)
        ~f:(fun (code, data) (r, bytes) ->
          let mem =
            Memory.create endian
              (Addr.of_int64 ~width r.lower)
              (Bigstring.of_string bytes)
            |> Or_error.ok_exn
          in
          let tag = Value.create Image.section (region_name r) in
          if selected ?regions r then (Memmap.add code mem tag, data)
          else (code, Memmap.add data mem tag))
    in
    (* the specification of the file, with the names of the script, and
       the roots, which the disassembler names by their addresses *)
    let spec =
      let facts =
        Ogre.sequence
          (List.concat_map (names t symbols) ~f:(fun (name, addr) ->
               [
                 Ogre.provide Image.Scheme.code_start addr;
                 Ogre.provide Image.Scheme.named_symbol addr name;
               ])
          @ List.map roots ~f:(Ogre.provide Image.Scheme.code_start))
      in
      Ogre.exec facts (Project.specification t.project) |> Or_error.ok_exn
    in
    incr projects;
    let file = Option.value (Project.get t.project filename) ~default:"a.out" in
    let filename = sprintf "%s#live%d" file !projects in
    match
      Project.create ~package:filename
        (Project.Input.custom ~filename ~code ~data ~spec target)
    with
    | Ok proj -> Bap_emu_xrefs.set_project_digest proj digest
    | Error err -> failwithf "Bap_emu.project: %s" (Error.to_string_hum err) ()
  in
  (* the cache has the project of the same code, or gets it *)
  match cache with
  | None -> build ()
  | Some file -> (
      match load_project file with
      | proj when Option.equal String.equal (project_digest proj) (Some digest)
        ->
          proj
      | _ | (exception Failure _) ->
          let proj = build () in
          save_project proj file;
          proj)

type import = { slot : int64; name : string; value : int64 option }

(* the slots of the relocations of the external functions, which the
   loader resolved, and the addresses, that they hold now *)
let imports t =
  let e = engine t in
  let externals =
    match t.session.recipe with Some (_, _, xs) -> xs | None -> []
  in
  let word slot =
    match read t slot e.bytes with
    | exception Invalid_argument _ -> None
    | data ->
        let bytes = if e.big_endian then data else String.rev data in
        Some
          (String.fold bytes ~init:0L ~f:(fun x c ->
               Int64.((x lsl 8) lor of_int (Char.to_int c))))
  in
  List.map externals ~f:(fun (slot, name) -> { slot; name; value = word slot })
  |> List.sort ~compare:(fun x y -> Int64.compare x.slot y.slot)

let function_at t addr = X.function_name (engine t) addr

(* the functions of the program, whose code runs again in Unicorn,
   instead of the stubs, that replaced them *)
let unstub t name =
  let own addr =
    Hashtbl.existsi t.session.own_code ~f:(fun ~key ~data:_ ->
        Int64.equal (X.int64_of_word key) addr)
  in
  let addrs =
    Hashtbl.to_alist t.session.names
    |> List.filter_map ~f:(fun (addr, data) ->
        Option.some_if (String.equal data name && own addr) addr)
  in
  if List.is_empty addrs then
    invalid_argf "Bap_emu.unstub: %s is not a function of the program" name ();
  let module Unstub (Machine : Primus.Machine.S) = struct
    module Exec = X.Make (Machine)

    let init () = Machine.List.iter addrs ~f:Exec.unstub
  end in
  primus t (module Unstub)

let arg t n =
  let name =
    match t.call with
    | Some name -> name
    | None -> invalid_arg "Bap_emu.arg: no function is called"
  in
  match Hashtbl.find t.session.signatures name with
  | Some { inputs; _ } -> (
      match List.nth inputs n with
      | Some exp ->
          accessible t 0L 0 (fun () ->
              Bitvec.to_int64 (Word.to_bitvec (X.eval_engine (engine t) exp)))
      | None -> invalid_argf "Bap_emu.arg: %s has no argument %d" name n ())
  | None -> invalid_argf "Bap_emu.arg: the prototype of %s is unknown" name ()

let exit_code t = t.session.exit_code

(* the threads are of the machine, see [X.threads] *)
let thread t =
  if not (paused t) then not_paused ~fn:"thread" t;
  let tid = ref 1 in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax

                let init () =
                  Machine.Local.get X.threads >>| fun { current; _ } ->
                  tid := current
              end);
  !tid

(* the thread, that runs, at the address, at which it paused, and the
   others, where they continue, by their TIDs *)
let changed_since t file =
  if not (paused t) then not_paused ~fn:"changed_since" t;
  match Checkpoint.C.load file with
  | Error msg -> failwith msg
  | Ok (c : Checkpoint.C.t) ->
      let theirs =
        Primus.Memory.Snapshot.values c.memory
        |> List.map ~f:(fun (addr, x) ->
            (Bitvec.to_int64 (Word.to_bitvec addr), Word.to_int_exn x land 0xFF))
      in
      (* the bytes, that the checkpoint has, are compared with all bytes,
         also the generated ones, which the checkpoint keeps as stored,
         and the other bytes only with the stored ones, as the ones,
         that the loads generated since, aren't changes *)
      let table values =
        let t = Int64.Table.create () in
        List.iter values ~f:(fun (key, data) -> Hashtbl.set t ~key ~data);
        t
      in
      let all = table (values ~generated:true t None) in
      let stored = table (values t None) in
      let theirs = table theirs in
      let differ a b =
        Hashtbl.fold a ~init:[] ~f:(fun ~key ~data acc ->
            match Hashtbl.find b key with
            | Some x when x = data -> acc
            | _ -> key :: acc)
      in
      let extra =
        Hashtbl.fold stored ~init:[] ~f:(fun ~key ~data:_ acc ->
            if Hashtbl.mem theirs key then acc else key :: acc)
      in
      coalesce (differ theirs all @ extra)

let threads t =
  if not (paused t) then not_paused ~fn:"threads" t;
  let pc = pc t in
  let st = ref None in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax

                let init () =
                  Machine.Local.get X.threads >>| fun s -> st := Some s
              end);
  match !st with
  | None -> [ { Checkpoint.tid = 1; pc; waiting = None } ]
  | Some (s : X.threads) ->
      { Checkpoint.tid = s.current; pc; waiting = None }
      :: (List.map s.others ~f:(fun (o : X.thread) ->
              {
                Checkpoint.tid = o.tid;
                pc = o.next;
                waiting =
                  (match o.wait with
                  | Ready -> None
                  | Waiting addrs -> Some addrs);
              })
         |> List.sort ~compare:(fun (x : Checkpoint.thread) y ->
             Int.compare x.tid y.tid))

let thread_journal t =
  Queue.to_list t.session.thread_journal
  |> List.map ~f:(fun (event : X.journal_event) ->
      { kind = event.kind; detail = event.detail })

let maintenance_stats t =
  if not (paused t) then not_paused ~fn:"maintenance_stats" t;
  let snapshot (operation : X.operation) =
    { count = operation.count; seconds = operation.seconds }
  in
  let zero () = { count = 0; seconds = 0. } in
  let lift_cleanup = snapshot t.lift_cleanup in
  let block_reclamation = snapshot t.block_reclamation in
  let heap_compaction = snapshot t.heap_compaction in
  match t.session.lifter with
  | None ->
      {
        lru_reconstruction = zero ();
        entry_eviction = zero ();
        cache_load = zero ();
        cache_merge = zero ();
        cache_write = zero ();
        lift_cleanup;
        block_reclamation;
        heap_compaction;
        cache_entries_written = 0;
        cache_bytes_written = 0;
      }
  | Some lifter ->
      let maintenance = lifter.maintenance () in
      {
        lru_reconstruction = snapshot maintenance.lru_reconstruction;
        entry_eviction = snapshot maintenance.entry_eviction;
        cache_load = snapshot maintenance.cache_load;
        cache_merge = snapshot maintenance.cache_merge;
        cache_write = snapshot maintenance.cache_write;
        lift_cleanup;
        block_reclamation;
        heap_compaction;
        cache_entries_written = maintenance.cache_entries_written;
        cache_bytes_written = maintenance.cache_bytes_written;
      }

let execution_stats t =
  if not (paused t) then not_paused ~fn:"execution_stats" t;
  let last_pc = pc t in
  let active_threads = List.length (threads t) in
  let stack = ref None in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax

                let init () =
                  Machine.Local.get X.call_sites >>= fun sites ->
                  Machine.Local.get X.last_call_stack >>| fun last ->
                  let current =
                    match sites with
                    | (site : X.call_site) :: _ -> Some site.site_stack
                    | [] -> last
                  in
                  stack :=
                    Option.map current ~f:(fun (s : X.call_stack) ->
                        {
                          lower = s.lower;
                          upper = s.upper;
                          lowest_sp = s.lowest_sp;
                          max_usage = Int64.(s.upper - s.lowest_sp);
                        })
              end);
  let _, lifted_blocks, _ = Engine.inventory (engine t).engine in
  {
    instructions = t.instructions;
    lifted_blocks;
    active_threads;
    hook_dispatches = t.write_dispatches;
    rss = rss ();
    last_pc;
    stack = !stack;
  }

let start_stats t ~interval callback =
  if Float.(interval <= 0.) || not (Float.is_finite interval) then
    invalid_arg "Bap_emu.start_stats: invalid interval";
  if not (paused t) then not_paused ~fn:"start_stats" t;
  let subscription =
    {
      interval;
      callback;
      next = X.clock () +. interval;
      active = true;
      stop = (fun () -> ());
    }
  in
  let hooks = ref [] in
  let install (e : X.engine) =
    let fresh = instructions t in
    let hook =
      Engine.on_code e.engine (fun addr _ ->
          if subscription.active && fresh addr then begin
            t.instructions <- Int64.succ t.instructions;
            let now = X.clock () in
            if Float.(now >= subscription.next) then begin
              subscription.next <- now +. interval;
              defer t (fun t ->
                  if subscription.active then
                    subscription.callback (execution_stats t))
            end
          end)
    in
    hooks := hook :: !hooks
  in
  installed t install;
  let stop () =
    if subscription.active then begin
      subscription.active <- false;
      t.session.engine_hooks <-
        List.filter t.session.engine_hooks ~f:(fun g ->
            not (phys_equal g install));
      List.iter !hooks ~f:(fun hook ->
          try Engine.delete hook
          with Invalid_argument _ | Engine.Error _ -> ());
      hooks := []
    end
  in
  subscription.stop <- stop;
  scope t stop;
  subscription

let stop_stats subscription = subscription.stop ()

let start_maintenance (t : t) ~interval ?lift_cache_limit
    ?forget_lifts:(forget = false) ?(reclaim_blocks = false)
    ?(compact_heap = false) () =
  Option.iter lift_cache_limit ~f:(fun limit ->
      set_lift_cache_limit t (Some limit));
  start_stats t ~interval (fun _ ->
      if forget then forget_lifts t else save_lifts t;
      if reclaim_blocks then
        X.measure t.block_reclamation (fun () ->
            Engine.flush_tb (engine t).engine);
      if compact_heap then X.measure t.heap_compaction Gc.compact)

(* the registers of the thread, without the aliases: of the engine, for
   the thread, that runs, or the ones, that Primus keeps for the thread,
   that doesn't, see [X.Make.Threads.park] *)
let rec thread_regs t tid =
  if not (paused t) then not_paused ~fn:"thread_regs" t;
  List.sort (unsorted_thread_regs t tid) ~compare:(fun (a, _) (b, _) ->
      String.compare a b)

and unsorted_thread_regs t tid =
  let e = engine t in
  let basis = Target.Regs.basis e.regs in
  let value v =
    Option.bind (Target.Regs.read e.regs v) ~f:(fun w ->
        match Word.to_int64 w with
        | Ok x -> Some (Var.name v, x)
        | Error _ -> None)
  in
  if tid = thread t then List.filter_map basis ~f:value
  else if
    not
      (List.exists (threads t) ~f:(fun (th : Checkpoint.thread) -> th.tid = tid))
  then invalid_argf "Bap_emu.thread_regs: the program has no thread %d" tid ()
  else
    let regs = ref [] in
    primus t
      (module functor
                (Machine : Primus.Machine.S)
                ->
                struct
                  module Env = Primus.Env.Make (Machine)
                  open Machine.Syntax

                  let init () =
                    Machine.List.filter_map basis ~f:(fun v ->
                        let saved = X.thread_var tid v in
                        Env.is_set saved >>= function
                        | false -> Machine.return None
                        | true -> (
                            Env.get saved >>| fun x ->
                            match Word.to_int64 (Primus.Value.to_word x) with
                            | Ok value -> Some (Var.name v, value)
                            | Error _ -> None))
                    >>| fun saved -> regs := saved
                end);
    !regs

let require_thread t tid =
  if
    tid <> thread t
    && not
         (List.exists (threads t) ~f:(fun (th : Checkpoint.thread) ->
              th.tid = tid))
  then invalid_argf "Bap_emu: the program has no thread %d" tid ()

let backtrace ?thread:tid t =
  if not (paused t) then not_paused ~fn:"backtrace" t;
  let tid = Option.value tid ~default:(thread t) in
  require_thread t tid;
  let result = ref [] in
  primus t
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax

                let init () =
                  Machine.Local.get X.frames >>= fun frames ->
                  Machine.Local.get X.calls >>| fun calls ->
                  result :=
                    List.mapi frames ~f:(fun i _ ->
                        Option.value (List.nth calls i) ~default:(None, None))
              end);
  !result

let set_thread_reg t tid name value =
  if tid = thread t then set_reg t name value
  else
    let e = engine t in
    let basis = Target.Regs.basis e.regs in
    match List.find basis ~f:(fun v -> String.equal (Var.name v) name) with
    | None -> invalid_argf "Bap_emu: unknown register %s" name ()
    | Some v ->
        require_thread t tid;
        let width =
          match Var.typ v with
          | Type.Imm width -> width
          | _ -> invalid_argf "Bap_emu: register %s is not an integer" name ()
        in
        primus t
          (module functor
                    (Machine : Primus.Machine.S)
                    ->
                    struct
                      module Env = Primus.Env.Make (Machine)
                      module Value = Primus.Value.Make (Machine)
                      open Machine.Syntax

                      let init () =
                        let saved = X.thread_var tid v in
                        Value.of_word (Word.of_int64 ~width value)
                        >>= Env.set saved
                    end)

let set_thread_pc t tid addr =
  if tid = thread t then set_pc t addr
  else (
    require_thread t tid;
    primus t
      (module functor
                (Machine : Primus.Machine.S)
                ->
                struct
                  open Machine.Syntax

                  let init () =
                    Machine.Local.get X.threads >>= fun state ->
                    let others =
                      List.map state.others ~f:(fun (other : X.thread) ->
                          if other.tid = tid then { other with next = addr }
                          else other)
                    in
                    Machine.Local.put X.threads { state with others }
                end))

let resume_thread t tid =
  if tid <> thread t then begin
    require_thread t tid;
    let waiting =
      List.find_exn (threads t) ~f:(fun (th : Checkpoint.thread) ->
          th.tid = tid)
    in
    if Option.is_some waiting.waiting then
      invalid_argf "Bap_emu.resume_thread: thread %d is waiting" tid ();
    resume t (X.Resume_thread tid)
  end

type called =
  | Returned of int64
  | Parked of { pc : int64; thread : int }
  | Ended of status

(* the call, whose pauses are served, at most [budget] of them, and
   which tells, where it parked, if it still runs *)
let drive ?budget ?timeout ?stack ?args ?regs ?thread:tid ?service t addr =
  match
    call_served ~fn:"drive" ?budget ?timeout ?stack ?args ?regs ?thread:tid
      ?service t addr
  with
  | Some x -> Returned x
  | None -> (
      match status t with
      | Paused -> Parked { pc = pc t; thread = thread t }
      | s -> Ended s)

(* the system, whose program ended, finishes, as its knowledge is the
   result of the system *)
let knowledge t =
  (match t.state with Ended _ -> resume t (X.Continue 0L) | _ -> ());
  match t.state with Finished (Ok (_, _, kb)) -> Some kb | _ -> None

(* The taint of the values, that the program computes, which Primus
   tracks, see [Bap_taint], as the program runs in Unicorn, which leaves
   the code, that uses the tainted values, to Primus. *)
module Taint = struct
  open Bap_core_theory
  module T = Bap_taint.Std.Taint

  type place = Reg of string | Mem of int64 * int

  let components =
    [ "bap:propagate-taint-by-computation"; "bap:select-default-taint-policy" ]

  (* the variable of the register of the target, or of its base
     register, e.g., R0 for X0 or W0 of AArch64, as the code reads it *)
  let var target name =
    match Theory.Target.var target name with
    | None -> invalid_argf "Bap_emu: unknown register %s" name ()
    | Some v -> (
        match
          Option.bind (Theory.Target.unalias target v) ~f:Theory.Origin.cast_sub
        with
        | Some origin -> Var.reify (Theory.Origin.reg origin)
        | None -> Var.reify v)

  (* the place is checked, before the component runs, as its exceptions
     end the program *)
  let checked t place =
    match place with
    | Reg name -> ignore (var t.target name : Var.t)
    | Mem (_, len) when len < 0 ->
        invalid_argf "Bap_emu: the negative length %d" len ()
    | Mem _ -> ()

  let introduce t ~kind place =
    checked t place;
    let module Introduce (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Kind = T.Kind.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let init () =
        Kind.create kind >>= fun kind ->
        match place with
        | Reg name ->
            Machine.gets Project.target >>= fun target ->
            Env.get (var target name) >>= fun v ->
            Tracker.new_direct v kind >>| ignore
        | Mem (addr, len) ->
            Machine.gets Project.target >>= fun target ->
            let width = Theory.Target.code_addr_size target in
            Value.of_word (Word.of_int64 ~width addr) >>= fun addr ->
            Value.of_int ~width len >>= fun len ->
            Tracker.new_indirect ~addr ~len kind >>| ignore
    end in
    primus t (module Introduce)

  (* the kinds of the taints of the place *)
  let kinds t place =
    checked t place;
    let result = ref [] in
    let module Kinds (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Kind = T.Kind.Make (Machine)
      module Object = T.Object.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let names objects =
        Machine.List.map (Set.to_list objects) ~f:(fun obj ->
            Object.kind obj >>= Kind.name)

      let init () =
        Machine.gets Project.target >>= fun target ->
        (match place with
          | Reg name ->
              Env.get (var target name) >>= fun v ->
              Tracker.lookup v T.Rel.direct >>= names
          | Mem (addr, len) ->
              let width = Theory.Target.code_addr_size target in
              Machine.List.map (List.init len ~f:Fn.id) ~f:(fun i ->
                  Value.of_word (Word.of_int64 ~width Int64.(addr + of_int i))
                  >>= fun addr -> Tracker.lookup addr T.Rel.indirect >>= names)
              >>| List.concat)
        >>| fun kinds ->
        result := List.dedup_and_sort kinds ~compare:String.compare
    end in
    primus t (module Kinds);
    !result

  let is_tainted t ~kind place =
    List.mem (kinds t place) kind ~equal:String.equal

  let sanitize t ~kind place =
    checked t place;
    let module Sanitize (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Kind = T.Kind.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let init () =
        Kind.create kind >>= fun kind ->
        Machine.gets Project.target >>= fun target ->
        match place with
        | Reg name ->
            Env.get (var target name) >>= fun v ->
            Tracker.sanitize v T.Rel.direct kind
        | Mem (addr, len) ->
            let width = Theory.Target.code_addr_size target in
            Machine.List.iter (List.init len ~f:Fn.id) ~f:(fun i ->
                Value.of_word (Word.of_int64 ~width Int64.(addr + of_int i))
                >>= fun addr -> Tracker.sanitize addr T.Rel.indirect kind)
    end in
    primus t (module Sanitize)

  let on_jump t f =
    let module Observe (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Kind = T.Kind.Make (Machine)
      module Object = T.Object.Make (Machine)
      module Tracker = T.Tracker.Make (Machine)

      let jumped (cond, dst) =
        Tracker.lookup cond T.Rel.direct >>= fun objects ->
        if Set.is_empty objects then Machine.return ()
        else
          Machine.List.map (Set.to_list objects) ~f:(fun obj ->
              Object.kind obj >>= Kind.name)
          >>| fun kinds ->
          f t
            ~kinds:(List.dedup_and_sort kinds ~compare:String.compare)
            (Bitvec.to_int64 (Word.to_bitvec (Primus.Value.to_word dst)))

      let init () =
        Machine.Observation.observe Primus.Interpreter.jumping jumped
    end in
    primus t (module Observe)
end

(* The symbolic execution of the values, that the program computes from
   its inputs, which Primus tracks, see [Bap_primus_symbolic], as the
   program runs in Unicorn, which leaves the code, that uses the symbolic
   values, to Primus. *)
module Symbolic = struct
  open Bap_core_theory
  module S = Bap_primus_symbolic

  type place = Taint.place = Reg of string | Mem of int64 * int
  type model = (string * int64) list

  type branch = {
    addr : int64;
    taken : bool;
    condition : string;
    formula : S.SMT.formula;
    path : S.SMT.formula list;
    inputs : S.Input.t list;
  }

  let components = [ "bap:symbolic-computer"; "bap:symbolic-path-constraints" ]
  let to_int64 x = Bitvec.to_int64 (Word.to_bitvec x)

  let model inputs model =
    List.filter_map inputs ~f:(fun input ->
        S.SMT.Model.get model input
        |> Option.map ~f:(fun x ->
            (S.Input.to_symbol input, to_int64 (S.SMT.Value.to_word x))))

  (* the addresses of the bytes of the place in the memory *)
  let addresses target addr len =
    let width = Theory.Target.code_addr_size target in
    List.init len ~f:(fun i -> Word.of_int64 ~width Int64.(addr + of_int i))

  let symbolize t place =
    Taint.checked t place;
    let module Symbolize (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Mems = Primus.Memory.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Executor = S.Executor (Machine)

      (* the fresh value, whose formula is the input *)
      let input origin x =
        Value.of_word (Primus.Value.to_word x) >>= fun x ->
        Executor.set_input origin x >>| fun () -> x

      let init () =
        Machine.gets Project.target >>= fun target ->
        match place with
        | Reg name ->
            let v = Taint.var target name in
            Env.get v >>= input (S.Input.var v) >>= Env.set v
        | Mem (addr, len) ->
            Mems.memory >>= fun bank ->
            Machine.List.iter (addresses target addr len) ~f:(fun addr ->
                Mems.get addr
                >>= input (S.Input.ptr bank addr)
                >>= Mems.set addr)
    end in
    primus t (module Symbolize)

  let formula t place =
    Taint.checked t place;
    let result = ref [] in
    let module Formula (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Env = Primus.Env.Make (Machine)
      module Mems = Primus.Memory.Make (Machine)
      module Executor = S.Executor (Machine)

      let formula x =
        Executor.value x >>| Option.map ~f:(Format.asprintf "%a" S.SMT.pp_expr)

      let init () =
        Machine.gets Project.target >>= fun target ->
        (match place with
          | Reg name ->
              Env.get (Taint.var target name) >>= formula >>| List.return
          | Mem (addr, len) ->
              Machine.List.map (addresses target addr len) ~f:(fun addr ->
                  Mems.get addr >>= formula))
        >>| fun xs -> result := xs
    end in
    primus t (module Formula);
    !result

  let solve ?timeout t =
    let result = ref None in
    let module Solve (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Executor = S.Executor (Machine)
      module Constraints = S.Context.Make (Machine)

      let init () =
        Constraints.get S.Context.Scope.user >>= fun user ->
        Constraints.get S.Context.Scope.path >>= fun path ->
        Executor.inputs >>| fun inputs ->
        result :=
          S.SMT.check ?timeout (Set.to_list (Set.union user path))
          |> Option.map ~f:(model (Seq.to_list inputs))
    end in
    primus t (module Solve);
    !result

  let on_branch t f =
    let module Observe (Machine : Primus.Machine.S) = struct
      open Machine.Syntax
      module Eval = Primus.Interpreter.Make (Machine)
      module Value = Primus.Value.Make (Machine)
      module Executor = S.Executor (Machine)
      module Constraints = S.Context.Make (Machine)

      (* the observers, that come later, run first, so the constraints of
         the path don't have the condition yet *)
      let decided cond =
        Executor.value cond >>= function
        | None -> Machine.return ()
        | Some x ->
            let taken = not (Value.is_zero cond) in
            Eval.pc >>= fun pc ->
            Constraints.get S.Context.Scope.user >>= fun user ->
            Constraints.get S.Context.Scope.path >>= fun path ->
            Executor.inputs >>| fun inputs ->
            f t
              {
                addr = to_int64 pc;
                taken;
                condition = Format.asprintf "%a" S.SMT.pp_expr x;
                formula = S.SMT.formula ~refute:(not taken) x;
                path = Set.to_list (Set.union user path);
                inputs = Seq.to_list inputs;
              }

      let init () = Primus.Interpreter.eval_cond >>> decided
    end in
    primus t (module Observe)

  let addr b = b.addr
  let taken b = b.taken
  let condition b = b.condition

  let flip ?timeout b =
    S.SMT.check ?timeout (S.SMT.inverse b.formula :: b.path)
    |> Option.map ~f:(model b.inputs)
end

(* The shell, which reads the commands of the debugger, see bap:debugger,
   and runs them on the paused program, so that a script drops into it at
   a pause, e.g., at a breakpoint, and the user inspects and continues
   the program, see [shell]. *)

let shell_help =
  {|commands:
  c, continue [ADDR|NAME]  continue, to the address, or to the next stop
  s, step [N]              run N (1) instructions
  b, break ADDR|NAME       stop at the address, or the function
  d, delete ADDR|NAME      remove the breakpoint
  breaks                   list the breakpoints
  pc                       show the program counter, and its function
  regs                     show the registers, without the aliases
  reg NAME                 show the register
  set NAME VALUE           set the register
  x ADDR [LEN]             dump LEN (64) bytes of the memory
  write ADDR BYTE...       store the bytes to the memory
  insn ADDR                the instruction, that the lifted engine ran at the
                           address, with the bytes it was lifted from
  lifted ADDR [LEN]        dump LEN (64) bytes of the code, that the lifted
                           engine ran, as it was lifted
  bir ADDR                 the BIR of the instruction at the address, lifted
                           from the bytes, that the memory has
  call ADDR|NAME ARG...    call the function with the arguments, and show
                           its result
  sym [PREFIX]             the functions, whose names have the prefix
  regions                  the memory map
  origin ADDR              where the byte comes from: stored, generated,
                           mapped, or unmapped
  snap                     take a snapshot, and show its number
  restore [N]              restore the snapshot, the last by default
  save FILE                save the checkpoint
  q, quit                  leave the shell, after which the script goes on
  exit [CODE]              exit bap with CODE (0)
  help                     show this help
an ADDR is a number, e.g., 0x400000, a function, or a register|}

let number s = match Int64.of_string s with x -> Some x | exception _ -> None

(* the address: a number, the address of a function, or the value of a
   register *)
let resolve t s =
  match number s with
  | Some x -> Some x
  | None -> (
      match List.Assoc.find (symbols t) ~equal:String.equal s with
      | Some a -> Some a
      | None -> (
          match reg t s with
          | x -> Some x
          | exception Invalid_argument _ -> None))

(* the bytes, that are readable, by one, where the line isn't *)
let bytes_at t addr n =
  match read t addr n with
  | s -> List.map (String.to_list s) ~f:Option.some
  | exception Invalid_argument _ ->
      List.init n ~f:(fun i ->
          match read t Int64.(addr + of_int i) 1 with
          | s -> Some s.[0]
          | exception Invalid_argument _ -> None)

(* the lines of 16 bytes, as the debugger dumps them *)
let dump out base bytes =
  let say fmt = ksprintf out fmt in
  List.chunks_of bytes ~length:16
  |> List.iteri ~f:(fun i line ->
      let hex =
        List.map line ~f:(function
          | Some c -> sprintf "%02x" (Char.to_int c)
          | None -> "??")
      in
      let chars =
        List.map line ~f:(function
          | Some c when Char.is_print c -> c
          | _ -> '.')
      in
      say "%Lx: %-47s |%s|"
        Int64.(base + of_int Int.(i * 16))
        (String.concat ~sep:" " hex)
        (String.of_char_list chars))

let hex_bytes s =
  String.concat ~sep:" "
    (List.map (String.to_list s) ~f:(fun c -> sprintf "%02x" (Char.to_int c)))

(* the breakpoint stops the program at the address, in the engines of
   the emulator, see [installed], until it is removed, after which its
   hooks stay, idle *)
let add_break t addr =
  let addr = match arch t with Arm -> Int64.(addr land lnot 1L) | _ -> addr in
  if not (Hashtbl.mem t.shell.breaks addr) then begin
    let active = ref true in
    let install (e : X.engine) =
      let fresh = instructions t in
      ignore
        (Engine.on_code ~first:addr ~last:addr e.engine (fun a _ ->
             if !active && fresh a then stop t)
          : Engine.hook)
    in
    installed t install;
    Hashtbl.set t.shell.breaks ~key:addr ~data:(fun () ->
        active := false;
        t.session.engine_hooks <-
          List.filter t.session.engine_hooks ~f:(fun f ->
              not (phys_equal f install)))
  end

let delete_break t addr =
  let addr = match arch t with Arm -> Int64.(addr land lnot 1L) | _ -> addr in
  match Hashtbl.find_and_remove t.shell.breaks addr with
  | Some remove -> remove ()
  | None -> ()

(* where the program is, after a command, that ran it *)
let where out t =
  let say fmt = ksprintf out fmt in
  match status t with
  | Paused ->
      let pc = pc t in
      let f = try function_at t pc with Invalid_argument _ -> None in
      say "paused at %Lx%s" pc
        (Option.value_map f ~default:"" ~f:(( ^ ) " in "))
  | Running -> say "running"
  | Exited code ->
      say "exited%s" (Option.value_map code ~default:"" ~f:(sprintf " with %d"))
  | Failed msg -> say "failed: %s" msg

(* the registers of the target, without the aliases, e.g., EAX of RAX *)
let main_registers t =
  let module Theory = Bap_core_theory.Theory in
  let names =
    Theory.Target.regs ~exclude:[ Theory.Role.Register.alias ] t.target
    |> Set.to_list
    |> List.map ~f:Theory.Var.name
    |> String.Set.of_list
  in
  List.filter (registers t) ~f:(Set.mem names)

let show_reg out t name =
  let say fmt = ksprintf out fmt in
  say "%s = %s" name (Format.asprintf "%a" Word.pp_hex (reg_word t name))

(* runs the command, and tells, whether the shell stays *)
let execute t out words =
  let say fmt = ksprintf out fmt in
  let stay = true and leave = false in
  let with_addr s f =
    match resolve t s with
    | Some a -> f a
    | None -> say "%s is not an address" s
  in
  let len rest default =
    match rest with
    | [ n ] -> Option.value_map (number n) ~default ~f:Int64.to_int_exn
    | _ -> default
  in
  (match words with
  | [] -> ()
  | ("c" | "continue") :: rest ->
      (match rest with
      | [ point ] ->
          with_addr point (fun until -> ignore (run t ~until : status))
      | _ -> ignore (run t : status));
      where out t
  | ("s" | "step") :: rest ->
      let n = len rest 1 in
      let rec steps i =
        if i < n && Poly.equal (status t) Paused then begin
          ignore (step t : status);
          steps (i + 1)
        end
      in
      steps 0;
      where out t
  | ("b" | "break") :: [ point ] ->
      with_addr point (fun a ->
          add_break t a;
          say "breakpoint at %Lx" a)
  | ("d" | "delete") :: [ point ] -> with_addr point (delete_break t)
  | [ "breaks" ] ->
      Hashtbl.keys t.shell.breaks
      |> List.sort ~compare:Int64.compare
      |> List.iter ~f:(fun a ->
          say "%Lx%s" a
            (Option.value_map (function_at t a) ~default:"" ~f:(( ^ ) " ")))
  | [ "pc" ] -> where out t
  | [ "regs" ] -> List.iter (main_registers t) ~f:(show_reg out t)
  | [ "reg"; name ] -> show_reg out t name
  | [ "set"; name; value ] -> (
      match resolve t value with
      | Some x -> set_reg t name x
      | None -> say "%s is not a value" value)
  | "x" :: addr :: rest ->
      with_addr addr (fun a -> dump out a (bytes_at t a (len rest 64)))
  | "write" :: addr :: (_ :: _ as bytes) ->
      with_addr addr (fun a ->
          match
            List.map bytes ~f:(fun b ->
                match number b with
                | Some x when Int64.(x >= 0L && x < 256L) ->
                    Char.of_int_exn (Int64.to_int_exn x)
                | _ -> failwithf "%s is not a byte" b ())
          with
          | bytes -> write t a (String.of_char_list bytes)
          | exception Failure msg -> say "%s" msg)
  | [ "insn"; addr ] ->
      with_addr addr (fun a ->
          match insn_at t a with
          | Some i ->
              say "%s %s%s" i.name (hex_bytes i.bytes)
                (if i.thumb then " (thumb)" else "")
          | None -> say "the lifted engine ran nothing at %Lx" a)
  | "lifted" :: addr :: rest ->
      with_addr addr (fun a ->
          let code = lifted_bytes t a (len rest 64) in
          if String.is_empty code then
            say "the lifted engine ran nothing at %Lx" a
          else dump out a (List.map (String.to_list code) ~f:Option.some))
  | [ "bir"; addr ] ->
      with_addr addr (fun a ->
          match bir t a with
          | Some (size, blks) ->
              say "%d bytes" size;
              List.iter blks ~f:(fun blk -> say "%s" (Blk.to_string blk))
          | None -> say "not an instruction at %Lx" a)
  | "call" :: f :: args ->
      with_addr f (fun a ->
          match
            List.map args ~f:(fun x ->
                match resolve t x with
                | Some x -> x
                | None -> failwithf "%s is not an argument" x ())
          with
          | exception Failure msg -> say "%s" msg
          | args -> (
              match call t a ~args with
              | Some x -> say "%Ld (%Lx)" x x
              | None -> say "the call paused, see pc"))
  | "sym" :: rest ->
      let prefix = match rest with [ p ] -> p | _ -> "" in
      List.iter (symbols t) ~f:(fun (name, a) ->
          if String.is_prefix name ~prefix then say "%Lx %s" a name)
  | [ "regions" ] ->
      List.iter (regions t) ~f:(fun r ->
          say "%Lx-%Lx %c%c%c" r.lower r.upper
            (if r.readable then 'r' else '-')
            (if r.writable then 'w' else '-')
            (if r.executable then 'x' else '-'))
  | [ "origin"; addr ] ->
      with_addr addr (fun a ->
          say "%s"
            (match provenance t a with
            | Stored -> "stored"
            | Generated -> "generated"
            | Mapped -> "mapped"
            | Unmapped -> "unmapped"))
  | [ "snap" ] ->
      let snap = snapshot t in
      if Hash_set.mem t.session.dead snap.id then
        say "snapshot dropped by the retention limit"
      else (
        t.shell.snaps <- snap :: t.shell.snaps;
        say "snapshot %d" (List.length t.shell.snaps))
  | "restore" :: rest -> (
      let n = len rest (List.length t.shell.snaps) in
      match List.nth (List.rev t.shell.snaps) (n - 1) with
      | Some snap ->
          restore t snap;
          where out t
      | None -> say "no snapshot %d" n)
  | [ "save"; file ] ->
      save t file;
      say "saved"
  | ("q" | "quit") :: _ -> ()
  | "exit" :: rest -> Stdlib.exit (len rest 0)
  | _ -> say "%s" shell_help);
  match words with ("q" | "quit") :: _ -> leave | _ -> stay

(* a failed command, e.g., a store to a page, that isn't mapped, doesn't
   leave the shell *)
let execute t out words =
  try execute t out words
  with Invalid_argument msg | Failure msg ->
    out (sprintf "error: %s" msg);
    true

let rec shell ?(input = In_channel.stdin) ?(output = Out_channel.stdout)
    ?(prompt = "(emu) ") t =
  match t.state with
  | Running ->
      (* the shell opens at the pause, that the hook asks for *)
      defer t (fun t -> ignore (shell ~input ~output ~prompt t : status));
      status t
  | _ ->
      let out s =
        Out_channel.output_string output s;
        Out_channel.newline output;
        Out_channel.flush output
      in
      (* the commands of a file are shown, as the ones, that are typed,
         are *)
      let tty =
        try Caml_unix.isatty (Caml_unix.descr_of_in_channel input)
        with _ -> false
      in
      let rec loop () =
        Out_channel.output_string output prompt;
        Out_channel.flush output;
        match In_channel.input_line input with
        | None ->
            Out_channel.newline output;
            Out_channel.flush output
        | Some line ->
            if not tty then out line;
            let words =
              String.split_on_chars line ~on:[ ' '; '\t' ]
              |> List.filter ~f:(Fn.non String.is_empty)
            in
            if execute t out words then loop ()
      in
      loop ();
      status t
