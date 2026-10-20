open Core
open Bap_knowledge
open Bap.Std
open Bap_primus.Std
module X = Bap_primus_unicorn_plugin.Primus_unicorn_executor
module Native = Bap_primus_unicorn_plugin.Primus_unicorn_native
module Target = Bap_primus_unicorn_plugin.Primus_unicorn_target
module Uc = Bap_unicorn

type status = Paused | Exited of int option | Failed of string
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

type t = { mutable state : state; mutable call : string option }

let engine () =
  match !X.active with
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

let finish t state =
  t.state <- state;
  match state with
  | Suspended _ | Ended _ -> ()
  | Finished (Ok (_, _, kb)) ->
      Toplevel.set kb;
      X.driven := false
  | Finished (Error _) | Crashed _ -> X.driven := false

(* continues the paused system with the request *)
let resume t request =
  match t.state with
  | Suspended (_, _, k) -> finish t (Effect.Deep.continue k request)
  | Ended (_, k) -> finish t (Effect.Deep.continue k request)
  | _ -> invalid_arg "Bap_emu: the program is not paused"

let status t =
  match t.state with
  | Suspended _ -> Paused
  | Ended ((Primus.Normal | Exn Primus.Interpreter.Halt), _) ->
      Exited !X.exit_code
  | Ended (Exn exn, _) -> Failed (Primus.Exn.to_string exn)
  | Finished (Ok ((Primus.Normal | Exn Primus.Interpreter.Halt), _, _)) ->
      Exited !X.exit_code
  | Finished (Ok (Exn exn, _, _)) -> Failed (Primus.Exn.to_string exn)
  | Finished (Error conflict) ->
      Failed (Format.asprintf "%a" Knowledge.Conflict.pp conflict)
  | Crashed exn -> Failed (Exn.to_string exn)

let paused t = match t.state with Suspended _ -> true | _ -> false

(* the program runs from the entry, and, when it ends, the script may
   restore a snapshot, after which the machine, that ended, is killed,
   and the snapshot continues, which ends here too *)
let start (entry : Primus.Linker.name) =
  let module Machine = Primus.Analysis in
  let module Linker = Primus.Linker.Make (Machine) in
  let open Machine.Syntax in
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
    | X.Continue _ | X.Map _ | X.Snapshot | X.Store _ -> Machine.return ()
  in
  ended ()

let create ?(system = "bap:unicorn-executor") ?(components = []) ?(args = [])
    ?(envp = []) ?entry proj =
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
  let module Linker = Primus.Linker.Make (Primus.Analysis) in
  X.driven := true;
  X.pause := true;
  X.exit_code := None;
  X.engine_hooks := [];
  Hashtbl.clear X.call_hooks;
  let t = { state = Crashed (Failure "not started"); call = None } in
  finish t
    (fiber (fun () ->
         Primus.System.run system proj (Toplevel.current ())
           ~args:(Array.of_list (program :: args))
           ~envp:(Array.of_list envp) ~start:(start entry)));
  t

let pc t =
  match t.state with
  | Suspended (pc, _, _) -> pc
  | _ -> invalid_arg "Bap_emu: the program is not paused"

let set_pc t addr =
  match t.state with
  | Suspended (_, id, k) -> t.state <- Suspended (addr, id, k)
  | _ -> invalid_arg "Bap_emu: the program is not paused"

type snapshot = Primus.Machine.id

let machine t =
  match t.state with
  | Suspended (_, id, _) -> id
  | _ -> invalid_arg "Bap_emu: the program is not paused"

(* the machine, that takes the snapshot, forks, and stays paused, as the
   snapshot, and its fork continues *)
let snapshot t =
  let id = machine t in
  resume t X.Snapshot;
  id

let restore t snapshot =
  X.exit_code := None;
  resume t (X.Restore snapshot)

(* pauses the program before the next instruction, from a hook *)
let stop _ =
  let e = engine () in
  X.pause := true;
  e.reason <- Some X.Pause;
  Uc.stop e.uc

(* [fresh addr] if the instruction at [addr] is not the one that a hook
   saw last, which runs again, e.g., after its fault, when Unicorn starts
   anew *)
let instructions () =
  let last = ref None in
  fun addr ->
    let fresh =
      match !last with
      | Some (addr', start) -> not (Int64.equal addr addr' && start <> !X.starts)
      | None -> true
    in
    last := Some (addr, !X.starts);
    fresh

let installed f =
  X.engine_hooks := f :: !X.engine_hooks;
  Option.iter !X.active ~f

let run ?until t =
  if paused t then begin
    let e = engine () in
    let hook =
      Option.map until ~f:(fun addr ->
          (* the program, which is paused at the address, runs its
             instruction first *)
          let code =
            match e.arch with Arm -> Int64.(pc t land lnot 1L) | _ -> pc t
          in
          let skip = ref (Int64.equal addr code) in
          let fresh = instructions () in
          ( e,
            Uc.on_code e.uc ~first:addr ~last:addr (fun addr _ ->
                if fresh addr then if !skip then skip := false else stop t) ))
    in
    resume t (X.Continue (pc t));
    Option.iter hook ~f:(fun (e', hook) ->
        match !X.active with
        | Some e when phys_equal e e' -> Uc.delete e.uc hook
        | _ -> ())
  end;
  status t

let step t =
  if paused t then begin
    let e = engine () in
    let first = ref true in
    let fresh = instructions () in
    let hook =
      Uc.on_code e.uc (fun addr _ ->
          if fresh addr then if !first then first := false else stop t)
    in
    resume t (X.Continue (pc t));
    match !X.active with
    | Some e' when phys_equal e e' -> Uc.delete e.uc hook
    | _ -> ()
  end;
  status t

let registers _ = Target.Regs.names (engine ()).regs

let reg _ name =
  match Target.Regs.read_name (engine ()).regs name with
  | Some x -> Bitvec.to_int64 (Word.to_bitvec x)
  | None -> invalid_argf "Bap_emu: unknown register %s" name ()

let set_reg _ name x =
  if not (Target.Regs.write_name (engine ()).regs name (Word.of_int64 x)) then
    invalid_argf "Bap_emu: unknown register %s" name ()

(* the pages, which a paused program copies to Unicorn, as Primus has
   them *)
let rec accessible t addr n f =
  match f () with
  | x -> x
  | exception Native.Missing missing when paused t ->
      let page = X.page_of missing in
      resume t (X.Map missing);
      if Hashtbl.mem (engine ()).pages page then accessible t addr n f
      else invalid_argf "Bap_emu: %Lx is not mapped" missing ()
  | exception Native.Missing missing ->
      invalid_argf "Bap_emu: the page of %Lx is not in Unicorn yet" missing ()
  | exception Native.Denied ->
      invalid_argf "Bap_emu: the access to %d bytes at %Lx is denied" n addr ()

let read t addr n = accessible t addr n (fun () -> X.uc_read (engine ()) addr n)

let write t addr data =
  let n = String.length data in
  accessible t addr n (fun () ->
      let e = engine () in
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

let on_code ?first ?last t f =
  installed (fun e ->
      ignore (Uc.on_code ?first ?last e.uc (fun addr _ -> f t addr)))

let on_read ?first ?last t f =
  installed (fun e ->
      ignore
        (Uc.on_mem ?first ?last e.uc [ `read ] (fun _ addr size _ ->
             f t addr size)))

let on_write ?first ?last t f =
  installed (fun e ->
      ignore
        (Uc.on_mem ?first ?last e.uc [ `write ] (fun _ addr size value ->
             f t addr size value)))

let on_call t name f =
  let hook () =
    t.call <- Some name;
    Exn.protect
      ~f:(fun () ->
        match f t with Default -> X.Default | Return x -> X.Return x)
      ~finally:(fun () -> t.call <- None)
  in
  Hashtbl.add_multi X.call_hooks ~key:name ~data:hook;
  (* the functions of the program, which no stub replaces, are hooked at
     their addresses, the others stop Unicorn, see [X.call_returns] *)
  let foreign =
    match !X.recipe with Some (_, foreign, _) -> foreign | None -> []
  in
  Hashtbl.iteri X.names ~f:(fun ~key:addr ~data ->
      if
        String.equal data name && not (List.mem foreign addr ~equal:Int64.equal)
      then
        installed (fun e ->
            ignore
              (Uc.on_code e.uc ~first:addr ~last:addr (fun _ _ ->
                   match X.call_returns e name with
                   | Some ret ->
                       e.reason <- Some (X.Jump ret);
                       Uc.stop e.uc
                   | None -> ()))))

let arg t n =
  let name =
    match t.call with
    | Some name -> name
    | None -> invalid_arg "Bap_emu.arg: no function is called"
  in
  match Hashtbl.find X.signatures name with
  | Some { inputs; _ } -> (
      match List.nth inputs n with
      | Some exp ->
          accessible t 0L 0 (fun () ->
              Bitvec.to_int64 (Word.to_bitvec (X.eval_uc (engine ()) exp)))
      | None -> invalid_argf "Bap_emu.arg: %s has no argument %d" name n ())
  | None -> invalid_argf "Bap_emu.arg: the prototype of %s is unknown" name ()

let exit_code _ = !X.exit_code

(* The taint of the values, that the program computes, which Primus
   tracks, see [Bap_taint], as the program runs in Unicorn, which leaves
   the code, that uses the tainted values, to Primus. *)
module Taint = struct
  open Bap_core_theory
  module T = Bap_taint.Std.Taint

  type place = Reg of string | Mem of int64 * int

  let components =
    [ "bap:propagate-taint-by-computation"; "bap:select-default-taint-policy" ]

  (* the variable of the register of the target *)
  let var target name =
    match Theory.Target.var target name with
    | Some v -> Var.reify v
    | None -> invalid_argf "Bap_emu.Taint: unknown register %s" name ()

  let introduce t ~kind place =
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
