open Core
open Bap_knowledge
open Bap.Std
open Bap_primus.Std
module X = Bap_primus_unicorn_plugin.Primus_unicorn_executor
module Native = Bap_primus_unicorn_plugin.Primus_unicorn_native
module Target = Bap_primus_unicorn_plugin.Primus_unicorn_target
module Uc = Bap_unicorn
module Io = Primus_lisp_library_plugin.Primus_lisp_io

type status = Paused | Running | Exited of int option | Failed of string
type action = Default | Return of int64

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
      (** the instructions, that [bir] lifted in the hooks *)
  hooked_calls : Int64.Hash_set.t;
      (** the addresses, whose calls the script hooks, see [on_call] *)
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

(* continues the paused system with the request *)
let resume t request =
  match t.state with
  | Suspended (_, _, k) | Ended (_, k) ->
      (* the hooks see, that the program runs, and its continuation is
         not resumed again *)
      t.state <- Running;
      finish t (Effect.Deep.continue k request)
  | _ -> invalid_arg "Bap_emu: the program is not paused"

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

let paused t = match t.state with Suspended _ -> true | _ -> false

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
    | X.Continue _ | X.Map _ | X.Snapshot | X.Store _ | X.Save _ ->
        Machine.return ()
  in
  ended ()

(* the components of [init], and the redirections run
   in the machine, after the components of the system, before the
   program starts, and the program continues from the checkpoint
   [restore], with its names, which the executor loads, when it starts.
   The system gets the session of the emulator with its project, see
   [X.with_session] *)
let create ?(system = "bap:unicorn-executor") ?(components = []) ?(init = [])
    ?(redirects = []) ?(args = []) ?(envp = []) ?entry ?restore proj =
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
    X.create_session ?restore:(Option.map restore ~f:Option.return) ()
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
      lifted = Hashtbl.Poly.create ();
      hooked_calls = Int64.Hash_set.create ();
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
  | _ -> invalid_arg "Bap_emu: the program is not paused"

let set_pc t addr =
  match t.state with
  | Suspended (_, id, k) -> t.state <- Suspended (addr, id, k)
  | _ -> invalid_arg "Bap_emu: the program is not paused"

(* the machine, which is of the system of the emulator, as the systems
   number their machines alike *)
type snapshot = { owner : X.session; id : Primus.Machine.id }

let machine t =
  match t.state with
  | Suspended (_, id, _) -> id
  | _ -> invalid_arg "Bap_emu: the program is not paused"

(* the machine, that takes the snapshot, forks, and stays paused, as the
   snapshot, and its fork continues *)
let snapshot t =
  let id = machine t in
  resume t X.Snapshot;
  { owner = t.session; id }

let restore t { owner; id } =
  if not (phys_equal owner t.session) then
    invalid_arg "Bap_emu.restore: the snapshot is of another emulator";
  t.session.exit_code <- None;
  resume t (X.Restore id)

module type Completion = X.Completion

let complete = X.complete

let save t file =
  if not (paused t) then
    invalid_arg "Bap_emu.save: the program is not paused, e.g., in a hook";
  resume t (X.Save (file, pc t));
  match t.session.saved with Ok () -> () | Error msg -> failwith msg

(* pauses the program before the next instruction, from a hook *)
let stop t =
  let e = engine t in
  t.session.pause <- true;
  e.reason <- Some X.Pause;
  Uc.stop e.uc

(* [fresh addr] if the instruction at [addr] is not the one that a hook
   saw last, which runs again, e.g., after its fault, when Unicorn starts
   anew *)
let instructions t =
  let last = ref None in
  fun addr ->
    let starts = t.session.starts in
    let fresh =
      match !last with
      | Some (addr', start) -> not (Int64.equal addr addr' && start <> starts)
      | None -> true
    in
    last := Some (addr, starts);
    fresh

(* the hook goes to the engine of the emulator, and to its new engines,
   see [X.session] *)
let installed t f =
  t.session.engine_hooks <- f :: t.session.engine_hooks;
  Option.iter t.session.active ~f

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
            Uc.on_code e.uc ~first:addr ~last:addr (fun addr _ ->
                if fresh addr then if !skip then skip := false else stop t) ))
    in
    resume t (X.Continue (pc t));
    Option.iter hook ~f:(fun (e', hook) ->
        match t.session.active with
        | Some e when phys_equal e e' -> Uc.delete e.uc hook
        | _ -> ())
  end;
  status t

let step t =
  if paused t then begin
    let e = engine t in
    let first = ref true in
    let fresh = instructions t in
    let hook =
      Uc.on_code e.uc (fun addr _ ->
          if fresh addr then if !first then first := false else stop t)
    in
    resume t (X.Continue (pc t));
    match t.session.active with
    | Some e' when phys_equal e e' -> Uc.delete e.uc hook
    | _ -> ()
  end;
  status t

let registers t = Target.Regs.names (engine t).regs

let reg t name =
  match Target.Regs.read_name (engine t).regs name with
  | Some x -> Bitvec.to_int64 (Word.to_bitvec x)
  | None -> invalid_argf "Bap_emu: unknown register %s" name ()

let set_reg t name x =
  if not (Target.Regs.write_name (engine t).regs name (Word.of_int64 x)) then
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
      invalid_argf "Bap_emu: the page of %Lx is not in Unicorn yet" missing ()
  | exception Native.Denied ->
      invalid_argf "Bap_emu: the access to %d bytes at %Lx is denied" n addr ()

let read t addr n = accessible t addr n (fun () -> X.uc_read (engine t) addr n)

let write t addr data =
  let n = String.length data in
  accessible t addr n (fun () ->
      let e = engine t in
      if X.uc_readable e addr n < n then raise Native.Denied;
      X.uc_write e addr data;
      (* the code, which Unicorn translated, is translated anew *)
      let code =
        List.exists
          [ X.page_of addr; X.page_of Int64.(addr + of_int n - 1L) ]
          ~f:(fun page ->
            match Hashtbl.find e.pages page with
            | Some { perm; _ } -> Uc.Perm.mem perm Uc.Perm.exec
            | None -> false)
      in
      if code then Uc.flush_tb e.uc)

(* the bytes go to Primus, from which they go to Unicorn, see
   [X.backing], and the code, that it translated, is translated anew *)
let patch t addr data =
  if not (paused t) then
    invalid_arg "Bap_emu.patch: the program is not paused, e.g., in a hook";
  (* the bytes are mapped and readable *)
  ignore (read t addr (String.length data) : string);
  resume t (X.Store (addr, data))

(* the component runs in the machine, which is paused, or ended *)
let primus t component =
  match t.state with
  | Suspended _ | Ended _ -> resume t (X.Run component)
  | _ ->
      invalid_arg "Bap_emu.primus: the program is not paused, e.g., in a hook"

(* the instruction in a hook, while the machine runs the program, is
   lifted outside of it, as the script does, in the knowledge, that
   starts from the toplevel one, and keeps the semantics, e.g., the Lisp
   program of x86, which it loads once, and the instructions, which are
   cached by their addresses and bytes *)
let hooked t ?encoding ~thumb addr bytes =
  let key = (addr, bytes, thumb) in
  match Hashtbl.find t.lifted key with
  | Some insn -> insn
  | None ->
      let toplevel = Toplevel.current () in
      let result = ref None in
      Toplevel.set (Option.value t.hooked ~default:toplevel);
      Exn.protect
        ~finally:(fun () ->
          t.hooked <- Some (Toplevel.current ());
          Toplevel.set toplevel)
        ~f:(fun () ->
          Toplevel.exec
            Knowledge.Syntax.(
              Primus.Lift.instruction ?encoding t.project addr bytes
              >>| fun insn -> result := insn));
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
  let read a n =
    let off = Int64.(to_int_exn (a - addr)) in
    if off < 0 || off >= String.length bytes then ""
    else String.sub bytes ~pos:off ~len:(min n (String.length bytes - off))
  in
  let encoding =
    match e.arch with Arm -> Primus.Interworking.encoding ~thumb | _ -> None
  in
  match t.state with
  | Running -> hooked t ?encoding ~thumb addr bytes
  | _ ->
      let result = ref None in
      primus t
        (module functor
                  (Machine : Primus.Machine.S)
                  ->
                  struct
                    module Lift = Primus.Lift.Make (Machine)
                    open Machine.Syntax

                    let init () =
                      Lift.insn ?encoding ~read addr >>| fun insn ->
                      result := insn
                  end);
      !result

let on_code ?first ?last t f =
  installed t (fun e ->
      ignore (Uc.on_code ?first ?last e.uc (fun addr _ -> f t addr)))

let on_read ?first ?last t f =
  installed t (fun e ->
      ignore
        (Uc.on_mem ?first ?last e.uc [ `read ] (fun _ addr size _ ->
             f t addr size)))

let on_write ?first ?last t f =
  installed t (fun e ->
      ignore
        (Uc.on_mem ?first ?last e.uc [ `write ] (fun _ addr size value ->
             f t addr size value)))

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
        let seen = ref (-1) in
        ignore
          (Uc.on_code e.uc ~first:addr ~last:addr (fun addr _ ->
               let s = t.session in
               let again =
                 Option.equal Int64.equal s.restarted_at (Some addr)
                 && !seen = s.starts - 1
               in
               seen := s.starts;
               if not (again || Hash_set.mem e.foreign addr) then
                 match
                   Option.bind (Hashtbl.find s.names addr) ~f:(X.call_returns e)
                 with
                 | Some ret ->
                     e.reason <- Some (X.Jump ret);
                     Uc.stop e.uc
                 | None -> ())))
  end

let on_call t name f =
  let hook () =
    t.call <- Some name;
    Exn.protect
      ~f:(fun () ->
        match f t with Default -> X.Default | Return x -> X.Return x)
      ~finally:(fun () -> t.call <- None)
  in
  Hashtbl.add_multi t.session.call_hooks ~key:name ~data:hook;
  Hashtbl.iteri t.session.names ~f:(fun ~key:addr ~data ->
      if String.equal data name then hook_calls t addr)

(* the name goes to the checkpoints, and replaces the name, that the
   address had, e.g., of the program *)
let add_symbol t name addr =
  Hashtbl.set t.session.symbols ~key:addr ~data:name;
  Hashtbl.set t.session.names ~key:addr ~data:name;
  if Hashtbl.mem t.session.call_hooks name then hook_calls t addr

let symbols t =
  Hashtbl.to_alist t.session.names
  |> List.sort ~compare:(fun (a, _) (b, _) -> Int64.compare a b)
  |> List.map ~f:(fun (addr, name) -> (name, addr))

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
              Bitvec.to_int64 (Word.to_bitvec (X.eval_uc (engine t) exp)))
      | None -> invalid_argf "Bap_emu.arg: %s has no argument %d" name n ())
  | None -> invalid_argf "Bap_emu.arg: the prototype of %s is unknown" name ()

let exit_code t = t.session.exit_code

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
