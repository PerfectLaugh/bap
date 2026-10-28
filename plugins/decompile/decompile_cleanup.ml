open Core
module Ast = Decompile_ast

let rec pure expression =
  match expression.Ast.node with
  | Ast.Var _ | Ast.Const _ | Ast.Address _ -> true
  | Ast.Unary (_, x) | Ast.Cast (_, x) -> pure x
  | Ast.Binary (_, x, y) -> pure x && pure y
  | Ast.Conditional (c, x, y) -> pure c && pure x && pure y
  | Ast.Aggregate fields ->
      List.for_all fields ~f:(fun (_, value) -> pure value)
  | Ast.Deref _ | Ast.Field _ | Ast.Index _ | Ast.Call _ | Ast.Machine _
  | Ast.Raw_exp _ ->
      false

let rec expression_variables variables expression =
  let variables =
    match expression.Ast.node with
    | Ast.Var { Ast.typ = Ast.Function _; _ } -> variables
    | Ast.Var variable -> Set.add variables variable.Ast.id
    | _ -> variables
  in
  match expression.Ast.node with
  | Ast.Var _ | Ast.Const _ | Ast.Raw_exp _ -> variables
  | Ast.Unary (_, x) | Ast.Cast (_, x) | Ast.Deref x | Ast.Address x ->
      expression_variables variables x
  | Ast.Binary (_, x, y) ->
      expression_variables (expression_variables variables x) y
  | Ast.Field (x, _, _) -> expression_variables variables x
  | Ast.Index (x, index) ->
      expression_variables (expression_variables variables x) index
  | Ast.Call { target; arguments; _ } ->
      List.fold arguments
        ~init:(expression_variables variables target)
        ~f:expression_variables
  | Ast.Conditional (c, x, y) ->
      expression_variables
        (expression_variables (expression_variables variables c) x)
        y
  | Ast.Aggregate fields ->
      List.fold fields ~init:variables ~f:(fun variables (_, value) ->
          expression_variables variables value)
  | Ast.Machine (_, xs) -> List.fold xs ~init:variables ~f:expression_variables

let rec statement_variables variables statement =
  match statement with
  | Ast.Decl _ | Ast.Break | Ast.Continue | Ast.Label _ | Ast.Goto _
  | Ast.Raw_jump _ | Ast.Comment _ ->
      variables
  | Ast.Assign (left, right) -> (
      let variables = expression_variables variables right in
      match left.Ast.node with
      | Ast.Var _ -> variables
      | _ -> expression_variables variables left)
  | Ast.Expr expression -> expression_variables variables expression
  | Ast.Return None -> variables
  | Ast.Return (Some expression) -> expression_variables variables expression
  | Ast.If (condition, yes, no) ->
      statements_variables
        (statements_variables (expression_variables variables condition) yes)
        no
  | Ast.While (condition, body) ->
      statements_variables (expression_variables variables condition) body
  | Ast.Do_while (body, condition) ->
      statements_variables (expression_variables variables condition) body
  | Ast.Switch (value, cases, default) ->
      let variables = expression_variables variables value in
      let variables =
        List.fold cases ~init:variables ~f:(fun variables (_, body) ->
            statements_variables variables body)
      in
      Option.value_map default ~default:variables
        ~f:(statements_variables variables)

and statements_variables variables statements =
  List.fold statements ~init:variables ~f:statement_variables

let used_variables = statements_variables Int.Set.empty

let negate expression =
  { expression with Ast.node = Ast.Unary ("!", expression) }

let type_width = function
  | Ast.Unknown bits | Ast.Int (bits, _) | Ast.Float bits -> Some bits
  | _ -> None

let width_at_least left right =
  match (left, right) with Some left, Some right -> left >= right | _ -> false

let rec clean_expression expression =
  let node =
    match expression.Ast.node with
    | Ast.Var _ | Ast.Const _ | Ast.Raw_exp _ -> expression.Ast.node
    | Ast.Unary (operator, x) -> Ast.Unary (operator, clean_expression x)
    | Ast.Binary (operator, x, y) ->
        Ast.Binary (operator, clean_expression x, clean_expression y)
    | Ast.Cast (typ, x) -> Ast.Cast (typ, clean_expression x)
    | Ast.Deref x -> Ast.Deref (clean_expression x)
    | Ast.Address x -> Ast.Address (clean_expression x)
    | Ast.Field (x, field, offset) ->
        Ast.Field (clean_expression x, field, offset)
    | Ast.Index (x, index) ->
        Ast.Index (clean_expression x, clean_expression index)
    | Ast.Call { target; arguments; result } ->
        Ast.Call
          {
            target = clean_expression target;
            arguments = List.map arguments ~f:clean_expression;
            result;
          }
    | Ast.Conditional (condition, x, y) ->
        Ast.Conditional
          (clean_expression condition, clean_expression x, clean_expression y)
    | Ast.Aggregate fields ->
        Ast.Aggregate
          (List.map fields ~f:(fun (field, value) ->
               (field, clean_expression value)))
    | Ast.Machine (name, xs) ->
        Ast.Machine (name, List.map xs ~f:clean_expression)
  in
  match node with
  | Ast.Cast (typ, { node = Ast.Cast (inner, value); _ })
    when Option.equal Int.equal (type_width typ) (type_width inner)
         || width_at_least (type_width typ) (type_width inner) ->
      { expression with Ast.node = Ast.Cast (typ, value) }
  | Ast.Cast (typ, value) when Poly.equal typ value.Ast.typ -> value
  | _ -> { expression with Ast.node }

let remove_trailing_continue body =
  match List.last body with
  | Some Ast.Continue -> List.drop_last_exn body
  | _ -> body

let rec cleanup_statements ~bookkeeping statements =
  List.concat_map statements ~f:(cleanup_statement ~bookkeeping)

and cleanup_statement ~bookkeeping statement =
  let bookkeeping_variable expression =
    match expression.Ast.node with
    | Ast.Var variable -> Set.mem bookkeeping variable.Ast.name
    | _ -> false
  in
  let rec uses_bookkeeping expression =
    bookkeeping_variable expression
    ||
    match expression.Ast.node with
    | Ast.Var _ | Ast.Const _ | Ast.Raw_exp _ -> false
    | Ast.Unary (_, x) | Ast.Cast (_, x) | Ast.Deref x | Ast.Address x ->
        uses_bookkeeping x
    | Ast.Binary (_, x, y) -> uses_bookkeeping x || uses_bookkeeping y
    | Ast.Field (x, _, _) -> uses_bookkeeping x
    | Ast.Index (x, index) -> uses_bookkeeping x || uses_bookkeeping index
    | Ast.Call { target; arguments; _ } ->
        uses_bookkeeping target || List.exists arguments ~f:uses_bookkeeping
    | Ast.Conditional (c, x, y) ->
        uses_bookkeeping c || uses_bookkeeping x || uses_bookkeeping y
    | Ast.Aggregate fields ->
        List.exists fields ~f:(fun (_, value) -> uses_bookkeeping value)
    | Ast.Machine (_, xs) -> List.exists xs ~f:uses_bookkeeping
  in
  let statement =
    match statement with
    | Ast.Assign (left, right) ->
        Ast.Assign (clean_expression left, clean_expression right)
    | Ast.Expr expression -> Ast.Expr (clean_expression expression)
    | Ast.Return None -> statement
    | Ast.Return (Some expression) ->
        Ast.Return (Some (clean_expression expression))
    | Ast.If (condition, yes, no) -> Ast.If (clean_expression condition, yes, no)
    | Ast.While (condition, body) -> Ast.While (clean_expression condition, body)
    | Ast.Do_while (body, condition) ->
        Ast.Do_while (body, clean_expression condition)
    | Ast.Switch (value, cases, default) ->
        Ast.Switch (clean_expression value, cases, default)
    | _ -> statement
  in
  match statement with
  | Ast.Assign (left, _) when bookkeeping_variable left -> []
  | Ast.Assign ({ node = Ast.Deref address; _ }, { node = Ast.Const _; _ })
    when uses_bookkeeping address ->
      []
  | Ast.Assign ({ node = Ast.Var variable; _ }, { node = Ast.Var value; _ })
    when variable.Ast.id = value.Ast.id ->
      []
  | Ast.If (condition, yes, no) ->
      let yes =
        remove_trailing_continue (cleanup_statements ~bookkeeping yes)
      in
      let no = remove_trailing_continue (cleanup_statements ~bookkeeping no) in
      if List.is_empty yes && List.is_empty no then []
      else if List.is_empty yes then [ Ast.If (negate condition, no, []) ]
      else if List.is_empty no then [ Ast.If (condition, yes, []) ]
      else [ Ast.If (condition, yes, no) ]
  | Ast.While (condition, body) ->
      [
        Ast.While
          ( condition,
            remove_trailing_continue (cleanup_statements ~bookkeeping body) );
      ]
  | Ast.Do_while (body, condition) ->
      [
        Ast.Do_while
          ( remove_trailing_continue (cleanup_statements ~bookkeeping body),
            condition );
      ]
  | Ast.Switch (value, cases, default) ->
      [
        Ast.Switch
          ( value,
            List.map cases ~f:(fun (value, body) ->
                (value, cleanup_statements ~bookkeeping body)),
            Option.map default ~f:(cleanup_statements ~bookkeeping) );
      ]
  | _ -> [ statement ]

let rec remove_dead_scope used statements =
  let statements =
    List.map statements ~f:(fun statement ->
        match statement with
        | Ast.If (condition, yes, no) ->
            Ast.If
              (condition, remove_dead_scope used yes, remove_dead_scope used no)
        | Ast.While (condition, body) ->
            Ast.While (condition, remove_dead_scope used body)
        | Ast.Do_while (body, condition) ->
            Ast.Do_while (remove_dead_scope used body, condition)
        | Ast.Switch (value, cases, default) ->
            Ast.Switch
              ( value,
                List.map cases ~f:(fun (value, body) ->
                    (value, remove_dead_scope used body)),
                Option.map default ~f:(remove_dead_scope used) )
        | _ -> statement)
  in
  List.filter statements ~f:(function
    | Ast.Assign ({ node = Ast.Var variable; _ }, value)
      when (not (Set.mem used variable.Ast.id)) && pure value ->
        false
    | _ -> true)

let rec remove_dead statements =
  let filtered = remove_dead_scope (used_variables statements) statements in
  if List.length filtered = List.length statements then statements
  else remove_dead filtered

let rec referenced_gotos statements =
  List.fold statements ~init:String.Set.empty ~f:(fun labels statement ->
      match statement with
      | Ast.Goto label -> Set.add labels label
      | Ast.If (_, yes, no) -> Set.union labels (referenced_gotos (yes @ no))
      | Ast.While (_, body) | Ast.Do_while (body, _) ->
          Set.union labels (referenced_gotos body)
      | Ast.Switch (_, cases, default) ->
          Set.union labels
            (referenced_gotos
               (List.concat_map cases ~f:snd @ Option.value default ~default:[]))
      | _ -> labels)

let remove_unused_labels statements =
  let labels = referenced_gotos statements in
  let rec clean statements =
    List.filter_map statements ~f:(fun statement ->
        match statement with
        | Ast.Label label when not (Set.mem labels label) -> None
        | Ast.If (condition, yes, no) ->
            Some (Ast.If (condition, clean yes, clean no))
        | Ast.While (condition, body) ->
            Some (Ast.While (condition, clean body))
        | Ast.Do_while (body, condition) ->
            Some (Ast.Do_while (clean body, condition))
        | Ast.Switch (value, cases, default) ->
            Some
              (Ast.Switch
                 ( value,
                   List.map cases ~f:(fun (value, body) -> (value, clean body)),
                   Option.map default ~f:clean ))
        | _ -> Some statement)
  in
  clean statements

let statements ?(bookkeeping = String.Set.empty) statements =
  cleanup_statements ~bookkeeping statements
  |> remove_dead |> remove_unused_labels
