open Core
open Bap.Std
open Result.Monad_infix

type operation = Add | Sub | And | Or | Xor

type state = {
  env : Bil.exp Var.Map.t;
  vars : Bil.var String.Map.t;
  writes : String.Set.t;
}

let initial =
  { env = Var.Map.empty; vars = String.Map.empty; writes = String.Set.empty }

let register_var vars var = Map.set vars ~key:(Var.name var) ~data:var

let register_exp vars exp =
  Set.fold (Exp.free_vars exp) ~init:vars ~f:register_var

let substitute env exp =
  Map.fold env ~init:exp ~f:(fun ~key ~data exp ->
      Exp.substitute (Bil.Var key) data exp)

let rec execute state = function
  | [] -> Ok state
  | Bil.Move (var, exp) :: rest ->
      let evaluated = substitute state.env exp in
      let state =
        {
          env = Map.set state.env ~key:var ~data:evaluated;
          vars = register_exp (register_var state.vars var) exp;
          writes =
            (if Var.is_physical var then Set.add state.writes (Var.name var)
             else state.writes);
        }
      in
      execute state rest
  | _ -> Error "only straight-line BIL Move statements can be validated"

let execute = execute initial

let output state name =
  match Map.find state.vars name with
  | None -> Error (sprintf "the BIL does not define %s" name)
  | Some var -> (
      match Map.find state.env var with
      | None -> Error (sprintf "the BIL does not define %s" name)
      | Some exp ->
          let free = Exp.free_vars exp in
          if Set.exists free ~f:Var.is_virtual then
            Error (sprintf "%s depends on an uninitialized temporary" name)
          else Ok exp)

let input state name =
  match Map.find state.vars name with
  | None -> Error (sprintf "the BIL does not contain input %s" name)
  | Some var -> Ok (Bil.Var var)

let check_writes ~expected state =
  let expected = String.Set.of_list expected in
  if Set.equal expected state.writes then Ok ()
  else
    Error
      (sprintf "unexpected architectural writes: expected %s, got %s"
         (String.concat ~sep:", " (Set.to_list expected))
         (String.concat ~sep:", " (Set.to_list state.writes)))

let operation_model = function
  | Add -> "Lifter.add"
  | Sub -> "Lifter.sub"
  | And -> "Lifter.logicalAnd"
  | Or -> "Lifter.logicalOr"
  | Xor -> "Lifter.logicalXor"

let operation_name = function
  | Add -> "ADD"
  | Sub -> "SUB"
  | And -> "AND"
  | Or -> "OR"
  | Xor -> "XOR"

let imm_width exp =
  match Type.infer exp with
  | Ok (Type.Imm width) -> Ok width
  | Ok (Type.Mem _ | Type.Unk) -> Error "the result is not an immediate"
  | Error error ->
      Error
        (sprintf "ill-typed result: %s"
           (Type.sexp_of_error error |> Sexp.to_string_hum))

let validate_reg_reg_with ~checker ~operation ~width ~destination ~left ~right
    bil =
  if not (List.mem [ 8; 16; 32; 64 ] width ~equal:Int.equal) then
    Error (sprintf "unsupported %s width %d" (operation_name operation) width)
  else
    execute bil >>= fun state ->
    check_writes ~expected:[ destination ] state >>= fun () ->
    input state left >>= fun left ->
    input state right >>= fun right ->
    output state destination >>= fun actual ->
    imm_width actual >>= fun result_width ->
    let model = operation_model operation in
    let application =
      if Int.equal result_width width then Ok (model, [ left; right ], [ model ])
      else if Int.equal width 32 && Int.equal result_width 64 then
        Ok
          ( sprintf "Lifter.result32 %s" model,
            [ left; right ],
            [ "Lifter.result32"; model ] )
      else
        Error
          (sprintf "operation width %d does not match result width %d" width
             result_width)
    in
    application >>= fun (function_name, arguments, unfold) ->
    Bil_lean.validate_application_with ~checker
      ~imports:[ "Lean"; "LifterProofs" ] ~function_name ~projection:None
      ~unfold actual arguments

let validate_reg_reg = validate_reg_reg_with ~checker:Bil_lean.check
