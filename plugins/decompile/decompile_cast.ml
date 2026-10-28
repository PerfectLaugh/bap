open Core
module Ast = Decompile_ast

let implied target source =
  match (target, source) with
  | Ast.Int (bits, Ast.Signed), Ast.Int (source, Ast.Signed) when bits = source
    ->
      true
  | Ast.Int (bits, (Ast.Unknown_sign | Ast.Unsigned)), Ast.Int (source, sign)
    -> (
      match (bits, source, sign) with
      | bits, source, _ when bits = source -> true
      | bits, source, Ast.Signed when bits <= source -> true
      | bits, source, _ when bits >= source -> true
      | _ -> false)
  | Ast.Bool, Ast.Bool -> true
  | target, source -> Poly.equal target source

let rec expression expr =
  match expr.Ast.node with
  | Ast.Cast (typ, value) ->
      let source_type = value.Ast.typ in
      let value = expression value in
      if implied typ source_type && implied typ value.Ast.typ then value
      else { expr with Ast.node = Ast.Cast (typ, value) }
  | _ ->
      let node =
        match expr.Ast.node with
        | Ast.Var _ | Ast.Const _ | Ast.Raw_exp _ -> expr.Ast.node
        | Ast.Unary (operator, value) -> Ast.Unary (operator, expression value)
        | Ast.Binary (operator, left, right) ->
            Ast.Binary (operator, expression left, expression right)
        | Ast.Cast _ -> assert false
        | Ast.Deref value -> Ast.Deref (expression value)
        | Ast.Address value -> Ast.Address (expression value)
        | Ast.Field (value, field, offset) ->
            Ast.Field (expression value, field, offset)
        | Ast.Index (value, index) ->
            Ast.Index (expression value, expression index)
        | Ast.Call { target; arguments; result } ->
            Ast.Call
              {
                target = expression target;
                arguments = List.map arguments ~f:expression;
                result;
              }
        | Ast.Conditional (condition, yes, no) ->
            Ast.Conditional (expression condition, expression yes, expression no)
        | Ast.Aggregate fields ->
            Ast.Aggregate
              (List.map fields ~f:(fun (field, value) ->
                   (field, expression value)))
        | Ast.Machine (name, values) ->
            Ast.Machine (name, List.map values ~f:expression)
      in
      { expr with Ast.node }

let rec statement = function
  | Ast.Assign (left, right) -> Ast.Assign (expression left, expression right)
  | Ast.Expr value -> Ast.Expr (expression value)
  | Ast.Return (Some value) -> Ast.Return (Some (expression value))
  | Ast.If (condition, yes, no) ->
      Ast.If (expression condition, statements yes, statements no)
  | Ast.While (condition, body) ->
      Ast.While (expression condition, statements body)
  | Ast.Do_while (body, condition) ->
      Ast.Do_while (statements body, expression condition)
  | Ast.Switch (value, cases, default) ->
      Ast.Switch
        ( expression value,
          List.map cases ~f:(fun (value, body) -> (value, statements body)),
          Option.map default ~f:statements )
  | statement -> statement

and statements values = List.map values ~f:statement

let program program =
  {
    program with
    Ast.functions =
      List.map program.Ast.functions ~f:(fun func ->
          { func with Ast.body = statements func.Ast.body });
  }
