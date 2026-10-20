open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Monads.Std
open Bap_main
include Self ()

let cutoff =
  Extension.Configuration.parameter
    Extension.Type.(int =? 1)
    "cutoff-level" ~doc:"The number of times the same branch is retried."

let timeout =
  Extension.Configuration.parameter
    Extension.Type.(int =? 16)
    "timeout"
    ~doc:
      "The number of milliseconds alloted to the SMT solver to find\n\
      \    a model"

open Bap_primus_symbolic

type edge = { blk : blk term; src : jmp term; dst : Jmp.dst }

type task = {
  constraints : Set.M(SMT.Formula).t;
  inputs : Set.M(Input).t;
  edge : edge option;
  id : tid;
}

type master = {
  self : Id.t option;
  ready : int;
  tasks : task Map.M(Int).t;
  tries : int Map.M(Tid).t;
}

type worker = { tid : tid; task : task }

let master =
  Primus.Machine.State.declare ~uuid:"8d2b41d4-4852-40e9-917a-33f1f5af01a1"
    ~name:"symbolic-executor-master"
  @@ fun _ ->
  {
    self = None;
    tasks = Int.Map.empty;
    tries = Tid.Map.empty;
    (* queued or finished forks *)
    ready = 0;
  }

let null = Tid.create ()

let worker =
  Primus.Machine.State.declare ~uuid:"92f3042c-ba8f-465a-9d57-4c1b9ec7c186"
    ~name:"symbolic-executor-worker"
  @@ fun _ ->
  {
    tid = null;
    task =
      {
        id = null;
        edge = None;
        constraints = Set.empty (module SMT.Formula);
        inputs = Set.empty (module Input);
      };
  }

let pp_dst ppf dst =
  match Jmp.resolve dst with
  | First tid -> Format.fprintf ppf "%a" Tid.pp tid
  | Second _ -> Format.fprintf ppf "unk"

let pp_edge ppf { blk; src; dst } =
  Format.fprintf ppf "%a(%a) -> %as" Tid.pp (Term.tid blk) Tid.pp (Term.tid src)
    pp_dst dst

let pp_edge_option ppf = function
  | None -> Format.fprintf ppf "sporadic"
  | Some edge -> pp_edge ppf edge

let pp_constraints ppf constrs =
  Set.iter constrs ~f:(Format.fprintf ppf "%a@\n" SMT.pp_formula)

let pp_task ppf { constraints = cs; edge; id } =
  Format.fprintf ppf "%a: %a s.t.@\n%a" Tid.pp id pp_edge_option edge
    pp_constraints cs

let forker ctxt : Primus.component =
  let cutoff = Extension.Configuration.get ctxt cutoff in
  let module Forker (Machine : Primus.Machine.S) = struct
    open Machine.Syntax
    module Executor = Executor (Machine)
    module Eval = Primus.Interpreter.Make (Machine)
    module Value = Primus.Value.Make (Machine)
    module Visited = Bap_primus_track_visited.Set.Make (Machine)
    module Constraints = Context.Make (Machine)
    module Debug = Debug (Machine)

    let is_conditional jmp =
      match Jmp.cond jmp with Bil.Int _ -> false | _ -> true

    (* is Some (blk,jmp) when the current position is a branch point *)
    let branch_point = function
      | Primus.Pos.Jmp { up = { me = blk }; me = jmp }
        when Term.length jmp_t blk > 1 ->
          Some (blk, jmp)
      | _ -> None

    let count table key =
      match Map.find table key with None -> 0 | Some x -> x

    let incr table key =
      Map.update table key ~f:(function None -> 1 | Some n -> n + 1)

    let is_visited visited dst =
      match Jmp.resolve dst with
      | Second _ -> false
      | First tid -> Set.mem visited tid

    let compute_edge pos =
      match branch_point pos with
      | None -> None
      | Some (blk, src) -> (
          let dst = match Jmp.alt src with None -> Jmp.dst src | dst -> dst in
          match dst with None -> None | Some dst -> Some { blk; src; dst })

    let is_edge_dst_visited visited { dst } = is_visited visited dst

    let append xs x =
      match Map.max_elt xs with
      | None -> Map.add_exn xs ~key:0 ~data:x
      | Some (k, _) -> Map.add_exn xs ~key:(k + 1) ~data:x

    let push_task task s = { s with tasks = append s.tasks task }

    let new_task ?edge ~refute constr =
      let constr = SMT.formula ~refute constr
      and contra = SMT.formula ~refute:(not refute) constr in
      Machine.Local.get worker >>= fun self ->
      if Set.mem self.task.constraints contra then Machine.return ()
      else
        Constraints.get Context.Scope.user >>= fun cs ->
        let constraints =
          let ( ++ ) = Set.union in
          Set.add (cs ++ self.task.constraints) constr
        in
        Executor.inputs >>= fun inputs ->
        let inputs = Seq.fold inputs ~init:self.task.inputs ~f:Set.add in
        let task = { inputs; constraints; edge; id = self.tid } in
        Machine.Global.update master ~f:(push_task task)

    let require cnd body = if cnd then body () else Machine.return ()

    let on_cond cond =
      Executor.value cond >>= function
      | None -> Machine.return ()
      | Some constr -> (
          Eval.pos >>| compute_edge >>= function
          | Some edge ->
              require (Value.is_zero cond) @@ fun () ->
              Visited.all >>= fun visited ->
              require (not (is_edge_dst_visited visited edge)) @@ fun () ->
              new_task ~refute:false ~edge constr
          | None ->
              Machine.Local.get worker >>= fun self ->
              Machine.Global.get master >>= fun s ->
              require (count s.tries self.tid < cutoff) @@ fun () ->
              new_task ~refute:(Value.is_one cond) constr)

    let pop_task () =
      let rec pop visited s ts =
        match Map.max_elt ts with
        | None -> None
        | Some (k, t) -> (
            let ts = Map.remove ts k in
            if
              count s.tries t.id > cutoff
              ||
              match t.edge with
              | None -> false
              | Some e -> is_edge_dst_visited visited e
            then pop visited s ts
            else
              match SMT.check (Set.to_list t.constraints) with
              | None -> pop visited s ts
              | Some m -> Some (m, t, ts))
      in
      Machine.Global.get master >>= fun s ->
      Visited.all >>= fun visited ->
      match pop visited s s.tasks with
      | None ->
          let ready = s.ready + Map.length s.tasks in
          report_progress ~stage:(ready - 1) ~total:ready ();
          Machine.Global.put master { s with tasks = Int.Map.empty }
          >>| fun () -> None
      | Some (m, t, ts) ->
          let queued = Map.length s.tasks in
          let left = Map.length ts in
          let processed = queued - left in
          report_progress
            ~stage:(s.ready + processed - 2)
            ~total:(s.ready + queued) ();
          Machine.Global.put master
            {
              s with
              tasks = ts;
              ready = s.ready + processed;
              tries = incr s.tries t.id;
            }
          >>| fun () -> Some (m, t)

    let exec_task model task =
      Debug.msg "SAT" >>= fun () ->
      Machine.Local.update worker ~f:(fun t -> { t with task }) >>= fun () ->
      let string_of_input = Input.to_symbol in
      let inputs = Set.to_sequence task.inputs in
      let module Input = Input.Make (Machine) in
      Machine.Seq.iter inputs ~f:(fun input ->
          match SMT.Model.get model input with
          | None -> Machine.return ()
          | Some value ->
              Debug.msg "%s = %a" (string_of_input input) SMT.pp_value value
              >>= fun () ->
              Value.of_word (SMT.Value.to_word value) >>= fun value ->
              Executor.set_input input value >>= fun () -> Input.set input value)

    let rec run_master system =
      Machine.Global.get master >>= fun s ->
      match s.self with
      | None ->
          Machine.current () >>= fun master_pid ->
          Debug.msg "starting the master process with pid %a" Id.pp master_pid
          >>= fun () ->
          Machine.Global.put master { s with self = Some master_pid }
          >>= fun () ->
          Machine.fork () >>= fun () ->
          Machine.current () >>= fun client_pid ->
          Debug.msg "the first fork returns at %a" Id.pp client_pid
          >>= fun () ->
          if Id.equal master_pid client_pid then run_master system
          else Machine.return ()
      | Some master_pid -> (
          pop_task () >>= function
          | None ->
              Debug.msg "Worklist is empty, finishing" >>= fun () ->
              Eval.halt >>| never_returns
          | Some (m, t) ->
              Debug.msg "We have some tasks" >>= fun () ->
              Machine.fork () >>= fun () ->
              Machine.current () >>= fun client_pid ->
              if Id.equal master_pid client_pid then
                Debug.msg "Client is finished, master is resumed" >>= fun () ->
                run_master system
              else Debug.msg "Forked a new machine" >>= fun () -> exec_task m t)

    let update_id t =
      Machine.Local.update worker ~f:(fun s -> { s with tid = t })

    let init () =
      Machine.sequence
        Primus.Interpreter.
          [
            eval_cond >>> on_cond;
            enter_term >>> update_id;
            Primus.System.start >>> run_master;
          ]
  end in
  (module Forker)

let sexp_of_assert_failure (name, model, inputs) =
  Sexp.List
    (Atom name
    :: List.filter_map inputs ~f:(fun input ->
        match SMT.Model.get model input with
        | None -> None
        | Some value ->
            Option.some
            @@ Sexp.List
                 [
                   Sexp.Atom (Input.to_symbol input);
                   Sexp.Atom (SMT.Value.to_string value);
                 ]))

let assert_failure, failed_assertion =
  Primus.Observation.provide "assert-failure" ~inspect:sexp_of_assert_failure
    ~desc:"occurs when a symbolic executor assertion doesn't hold"

let to_word x = Primus.Value.to_word x
let to_int x = to_word x |> Word.to_int_exn

module SymbolicPrimitives (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Lisp = Primus.Lisp.Make (Machine)
  module Mems = Primus.Memory.Make (Machine)
  module Val = Primus.Value.Make (Machine)
  module Env = Primus.Env.Make (Machine)
  module Executor = Executor (Machine)
  module Closure = Primus.Lisp.Closure.Make (Machine)
  module Constraints = Context.Make (Machine)
  module Debug = Debug (Machine)

  let addr_size arch_addr_size = function
    | [ addr_size; _data_size ] -> Ok (to_int addr_size)
    | [] | [ _ ] -> Ok arch_addr_size
    | _ -> Error "symbolic-memory: expects 3 to 5 arguments"

  let data_size = function
    | [ _addr_size; data_size ] -> to_int data_size
    | _ -> 8

  let register_memory m =
    let name = Bank.name m.bank in
    Machine.Global.update memories ~f:(fun mem ->
        Map.update mem name ~f:(function
          | None -> m
          | Some m' when equal_memory m m' -> m
          | _ ->
              invalid_argf
                "symbolic-memory: %s was previously defined with different \
                 parameters"
                name ()))

  let with_memory { bank } perform =
    Mems.memory >>= fun current ->
    Mems.switch bank >>= fun () ->
    perform >>= fun x ->
    Mems.switch current >>| fun () -> x

  let open_bank id =
    Machine.Global.get memories >>= fun mems ->
    Val.Symbol.of_value id >>= fun name ->
    match Map.find mems name with
    | None -> Lisp.failf "unknown memory %s" name ()
    | Some bank -> Machine.return bank

  let read id ptr =
    open_bank id >>= fun bank -> with_memory bank (Mems.get (to_word ptr))

  let write id ptr data =
    open_bank id >>= fun bank ->
    with_memory bank (Mems.set (to_word ptr) data) >>| fun () -> ptr

  let width default_width = function [] -> default_width | s :: _ -> to_int s

  let generator width = function
    | [ _; x ] ->
        let x = Word.to_int_exn @@ Primus.Value.to_word x in
        Primus.Generator.static ~width x
    | _ -> Primus.Generator.static ~width 0

  let arch_addr_size = Machine.gets Project.target >>| Theory.Target.bits

  let create_value var rest =
    arch_addr_size >>= fun default_width ->
    let width = width default_width rest in
    Val.Symbol.of_value var >>= fun name ->
    let var = Var.create name (Imm width) in
    Env.has var >>= function
    | true -> Env.get var
    | false -> Env.add var (generator width rest) >>= fun () -> Env.get var

  let create_memory id lower upper rest =
    let lower = to_word lower and upper = to_word upper in
    let data_size = data_size rest in
    arch_addr_size >>= fun arch_addr_size ->
    Val.Symbol.of_value id >>= fun name ->
    Machine.Global.get memories >>= fun memories ->
    if Map.mem memories name then Machine.return id
    else
      match addr_size arch_addr_size rest with
      | Error err -> Lisp.failf "symbolic-memory: %s" err ()
      | Ok addr_size ->
          let bank = Bank.create name ~addr_size ~data_size in
          let memory = { bank; lower; upper } in
          register_memory memory >>= fun () ->
          let width = Bank.data_size bank in
          let seed = Hashtbl.hash (Bank.name bank) in
          let generator = Primus.Generator.Random.lcg ~width seed in
          let region = Mems.add_region ~generator ~lower ~upper () in
          with_memory memory region >>| fun () -> id

  let assume assumptions =
    Machine.List.iter assumptions ~f:(fun x ->
        Executor.value x >>= function
        | Some x -> Constraints.add Context.Scope.user (SMT.formula x)
        | None ->
            (* should we raise on assert false? *)
            if Val.is_zero x then
              let false_ = SMT.word Word.b0 in
              Constraints.add Context.Scope.user (SMT.formula false_)
            else Machine.return ())
    >>= fun () -> Val.b1

  let assertion_of_value x =
    Executor.value x
    >>| ( function None -> SMT.word (Primus.Value.to_word x) | Some x -> x )
    >>| SMT.formula ~refute:true

  (* we can later add operators that manipulate the scopes
     in which the assertion is checked *)
  let assert_ name assertions =
    Machine.Observation.post failed_assertion ~f:(fun report ->
        Constraints.get Context.Scope.user >>= fun user ->
        Constraints.get Context.Scope.path >>= fun path ->
        let constraints = Set.to_list @@ Set.union user path in
        Machine.List.fold assertions ~init:constraints ~f:(fun constraints x ->
            assertion_of_value x >>| fun assertion -> assertion :: constraints)
        >>| SMT.check
        >>= function
        | None -> Machine.return ()
        | Some model ->
            Val.Symbol.of_value name >>= fun name ->
            Executor.inputs >>| Seq.to_list >>= fun inputs ->
            report (name, model, inputs))
    >>= fun () -> Val.b1

  let run args =
    Closure.name >>= fun name ->
    match (name, args) with
    | "symbolic-value", id :: rest -> create_value id rest
    | "symbolic-memory", id :: lower :: upper :: rest ->
        create_memory id lower upper rest
    | "symbolic-memory-read", [ id; ptr ] -> read id ptr
    | "symbolic-memory-write", [ id; ptr; data ] -> write id ptr data
    | "symbolic-assume", args -> assume args
    | "symbolic-assert", name :: args -> assert_ name args
    | _ -> Lisp.failf "%s: invalid number of arguments" name ()
end

module Primitives (Machine : Primus.Machine.S) = struct
  module Lisp = Primus.Lisp.Make (Machine)
  open Primus.Lisp.Type.Spec

  let def name types docs =
    Lisp.define name (module SymbolicPrimitives) ~types ~docs

  let init () =
    Machine.sequence
      [
        def "symbolic-assume"
          (all bool @-> bool)
          "Assumes the specified list of constraints.";
        def "symbolic-assert"
          ((one sym // all bool) @-> bool)
          "(assert NAME C1 ... CM) verifies the specified\n\
          \         list of assertions C1 and posts the assert-failure \
           observation\n\
          \         for each condition that doesn't hold.";
        def "symbolic-value"
          ((one sym // all int) @-> a)
          "(symbolic-value NAME &rest) creates a new symbolic value.\n\
          \        Accepts up to two optional arguments. The first argument\n\
          \        denotes the bitwidth of the created value and the second is\n\
          \        the initial value.";
        def "symbolic-memory"
          ((tuple [ sym; int; int ] // all int) @-> sym)
          "(symbolic-memory NAME LOWER UPPER &rest) creates a new\n\
          \        symbolic memory region with the given NAME and LOWER and \
           UPPER\n\
          \        bounds. The symbolic memory could be read and written with\n\
          \        the SYMBOLIC-MEMORY-READ and SYMBOLIC-MEMORY-WRITE \
           primitives.\n\
          \        Optionally accepts one or two more arguments. If two optional\n\
          \        arguments are provided, then the first one stands for the\n\
          \        address bus size of the symbolic memory and the second for \
           the\n\
          \        data bus size, all in bits. If only one is provided then it \
           is\n\
          \        interpreted as the data bus size and the address size \
           defaults\n\
          \        to the architecture-specific address size (e.g., 64 bits for\n\
          \        amd64). If none are provided then the address size is\n\
          \        architecture-specific and the data size defaults to 8 bits.";
        def "symbolic-memory-read"
          (tuple [ sym; int ] @-> byte)
          "(symbolic-memory-read MEM POS) reads the value of the\n\
          \         symbolic memory MEM at the specified position POS.";
        def "symbolic-memory-write"
          (tuple [ sym; int; byte ] @-> byte)
          "(symbolic-memory-write MEM POS X) writes X to the symbolic\n\
          \         memory MEM at the specified position POS.";
      ]
end

let () =
  Extension.declare ~doc:"provides a Primus symbolic executor"
    ~provides:[ "primus"; "symbolic-executor" ]
  @@ fun ctxt ->
  let open Extension.Syntax in
  SMT.set_timeout (ctxt --> timeout);
  Primus.Components.register_generic "symbolic-computer"
    (module Executor)
    ~package:"bap" ~desc:"Computes a symbolic formula for each Primus value.";
  Primus.Components.register_generic "symbolic-path-explorer" (forker ctxt)
    ~package:"bap"
    ~desc:
      "Computes a path constraint for each branch and forks a new machine if \
       the constraint is satisfiable.";
  Primus.Components.register_generic "symbolic-lisp-primitives" ~package:"bap"
    ~desc:"Provides assume and assert primitives."
    (module Primitives);
  Primus.Components.register_generic "symbolic-path-constraints" ~package:"bap"
    ~desc:
      "tracks the path constraint and records them in the machine's symbolic \
       context"
    (module Paths);
  Ok ()
