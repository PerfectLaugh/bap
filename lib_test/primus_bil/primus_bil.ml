open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Monads.Std

type t = { vars : word Var.Map.t; pc : word option }

module Machine = struct
  type 'a m = 'a

  include Primus.Machine.Make (Monad.Ident)
end

open Machine.Syntax
module Eval = Primus.Interpreter.Make (Machine)
module Env = Primus.Env.Make (Machine)
module Memory = Primus.Memory.Make (Machine)
module Value = Primus.Value.Make (Machine)

let rec storages = function
  | Bil.Var v -> [ v ]
  | Bil.Store (s, _, _, _, _) | Bil.Let (_, _, s) -> storages s
  | Bil.Ite (_, x, y) -> storages x @ storages y
  | _ -> []

let memories bil =
  object
    inherit [Var.Set.t] Stmt.visitor

    method! enter_load ~mem ~addr:_ _ _ ms =
      List.fold (storages mem) ~init:ms ~f:Set.add

    method! enter_store ~mem ~addr:_ ~exp:_ _ _ ms =
      List.fold (storages mem) ~init:ms ~f:Set.add
  end
    #run
    bil Var.Set.empty

let map_memory v =
  match Var.typ v with
  | Type.Mem (ks, vs) ->
      let addr_size = Size.in_bits ks and data_size = Size.in_bits vs in
      Memory.switch
        (Primus.Memory.Descriptor.create ~addr_size ~data_size (Var.name v))
      >>= fun () ->
      Memory.add_region ()
        ~generator:(Primus.Generator.static ~width:data_size 0)
        ~lower:(Word.zero addr_size) ~upper:(Word.ones addr_size)
  | Type.Imm _ | Type.Unk -> Machine.return ()

let init bil =
  Set.to_sequence (Bil.free_vars bil)
  |> Machine.Seq.iter ~f:(fun v ->
      match Var.typ v with
      | Type.Imm width -> Env.add v (Primus.Generator.static ~width 0)
      | Type.Mem _ | Type.Unk -> Env.add v (Primus.Generator.static 0))
  >>= fun () -> Set.to_sequence (memories bil) |> Machine.Seq.iter ~f:map_memory

let rec stmts pc = Machine.List.iter ~f:(stmt pc)

and stmt pc = function
  | Bil.Move (v, x) -> Eval.exp x >>= Eval.set v
  | Bil.Jmp dst -> Eval.exp dst >>| fun dst -> pc := Some (Value.to_word dst)
  | Bil.If (cond, yes, no) ->
      Eval.exp cond >>= fun cond ->
      stmts pc (if Word.is_one (Value.to_word cond) then yes else no)
  | Bil.While (cond, body) as loop ->
      Eval.exp cond >>= fun c ->
      if Word.is_one (Value.to_word c) then
        stmts pc body >>= fun () -> stmt pc loop
      else Machine.return ()
  | Bil.Special _ | Bil.CpuExn _ -> Machine.return ()

let assigned bil =
  object
    inherit [Var.Set.t] Stmt.visitor
    method! enter_move v _ vs = Set.add vs v
  end
    #run bil Var.Set.empty

let collect bil =
  Set.to_sequence (Set.union (Bil.free_vars bil) (assigned bil))
  |> Machine.Seq.fold ~init:Var.Map.empty ~f:(fun vars v ->
      Env.is_set v >>= function
      | false -> Machine.return vars
      | true ->
          Env.get v >>| fun x -> Map.set vars ~key:v ~data:(Value.to_word x))

let eval ?(target = Theory.Target.unknown) bil =
  let result = ref None and pc = ref None in
  let module System = Primus.System.Generic (Machine) in
  let start =
    init bil >>= fun () ->
    stmts pc bil >>= fun () ->
    collect bil >>| fun vars -> result := Some { vars; pc = !pc }
  in
  let system = Primus.System.define "bil-evaluator" ~package:"bap-test" in
  match (System.run ~start system (Project.empty target), !result) with
  | (Primus.Normal, _), Some r -> r
  | (Primus.Exn exn, _), _ ->
      failwithf "BIL evaluation failed: %s" (Primus.Exn.to_string exn) ()
  | (Primus.Normal, _), None -> failwith "BIL evaluation didn't finish"

let lookup { vars } v = Map.find vars v
let pc { pc } = pc
