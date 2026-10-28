open Core
open Bap.Std
module Ast = Decompile_ast

let rec map_expression f expression =
  let node =
    match expression.Ast.node with
    | Ast.Var _ | Ast.Const _ | Ast.Raw_exp _ -> expression.Ast.node
    | Ast.Unary (operator, x) -> Ast.Unary (operator, map_expression f x)
    | Ast.Binary (operator, x, y) ->
        Ast.Binary (operator, map_expression f x, map_expression f y)
    | Ast.Cast (typ, x) -> Ast.Cast (typ, map_expression f x)
    | Ast.Deref x -> Ast.Deref (map_expression f x)
    | Ast.Address x -> Ast.Address (map_expression f x)
    | Ast.Field (x, field, offset) ->
        Ast.Field (map_expression f x, field, offset)
    | Ast.Index (x, index) ->
        Ast.Index (map_expression f x, map_expression f index)
    | Ast.Call { target; arguments; result } ->
        Ast.Call
          {
            target = map_expression f target;
            arguments = List.map arguments ~f:(map_expression f);
            result;
          }
    | Ast.Conditional (condition, x, y) ->
        Ast.Conditional
          (map_expression f condition, map_expression f x, map_expression f y)
    | Ast.Aggregate fields ->
        Ast.Aggregate
          (List.map fields ~f:(fun (field, value) ->
               (field, map_expression f value)))
    | Ast.Machine (name, xs) ->
        Ast.Machine (name, List.map xs ~f:(map_expression f))
  in
  f { expression with Ast.node }

let is_zero expression =
  match expression.Ast.node with
  | Ast.Const value -> Word.is_zero value
  | _ -> false

let is_one expression =
  match expression.Ast.node with
  | Ast.Const value -> Word.is_one value
  | _ -> false

let integer_width = function
  | Ast.Bool -> Some 1
  | Ast.Int (bits, _) -> Some bits
  | _ -> None

let subtract_constant expression x value =
  {
    expression with
    Ast.node =
      Ast.Binary
        ("-", x, { node = Ast.Const (Word.neg value); typ = expression.Ast.typ });
  }

let rec simplify_expression expression =
  map_expression
    (fun expression ->
      match expression.Ast.node with
      | Ast.Cast (typ, { node = Ast.Cast (_, value); _ }) ->
          simplify_expression
            { expression with Ast.node = Ast.Cast (typ, value) }
      | Ast.Cast (Ast.Bool, value) -> value
      | Ast.Cast (Ast.Int (_, Ast.Signed), _) -> expression
      | Ast.Cast (Ast.Int (bits, _), value) -> (
          match integer_width value.Ast.typ with
          | Some source when source <= bits -> value
          | _ -> expression)
      | Ast.Binary ("==", { node = Ast.Binary ("==", x, zero); _ }, outer_zero)
        when is_zero zero && is_zero outer_zero ->
          { expression with Ast.node = Ast.Binary ("!=", x, zero) }
      | Ast.Binary ("==", { node = Ast.Binary ("!=", x, zero); _ }, outer_zero)
        when is_zero zero && is_zero outer_zero ->
          { expression with Ast.node = Ast.Binary ("==", x, zero) }
      | Ast.Binary
          ( "!=",
            { node = Ast.Binary ((("==" | "!=") as operator), x, zero); _ },
            outer_zero )
        when is_zero zero && is_zero outer_zero ->
          { expression with Ast.node = Ast.Binary (operator, x, zero) }
      | Ast.Binary ("+", x, y) when is_zero x || is_zero y ->
          if is_zero x then y else x
      | Ast.Binary ("+", x, { node = Ast.Const value; _ })
        when Word.is_negative (Word.signed value) ->
          subtract_constant expression x value
      | Ast.Binary ("+", { node = Ast.Const value; _ }, x)
        when Word.is_negative (Word.signed value) ->
          subtract_constant expression x value
      | Ast.Binary ("-", x, y) when is_zero y -> x
      | Ast.Binary ("*", x, y) when is_one x || is_one y ->
          if is_one x then y else x
      | Ast.Binary (("*" | "&"), x, y) when is_zero x || is_zero y ->
          if is_zero x then x else y
      | Ast.Binary (("|" | "^"), x, y) when is_zero x || is_zero y ->
          if is_zero x then y else x
      | (Ast.Binary ("<<", x, y) | Ast.Binary (">>", x, y)) when is_zero y -> x
      | Ast.Binary
          ( "|",
            {
              node =
                Ast.Binary
                  ( "<<",
                    {
                      node = Ast.Binary (">>", x, { node = Ast.Const high; _ });
                      _;
                    },
                    { node = Ast.Const low; _ } );
              _;
            },
            y )
        when Word.equal high low
             && Option.equal Int.equal (integer_width x.Ast.typ)
                  (Some (2 * Word.to_int_exn high)) ->
          y
      | Ast.Binary
          ( "|",
            { node = Ast.Binary ("<", a, b); _ },
            { node = Ast.Binary ("<", c, d); _ } )
        when Poly.equal a d && Poly.equal b c ->
          { expression with Ast.node = Ast.Binary ("!=", a, b) }
      | Ast.Binary ("==", x, y) when Poly.equal x y ->
          { expression with Ast.node = Ast.Const Word.b1 }
      | Ast.Binary ("!=", x, y) when Poly.equal x y ->
          { expression with Ast.node = Ast.Const Word.b0 }
      | Ast.Binary (("-" | "^"), x, y) when Poly.equal x y ->
          { expression with Ast.node = Ast.Const (Word.zero 32) }
      | Ast.Binary (("&" | "|"), x, y) when Poly.equal x y -> x
      | Ast.Binary ((("==" | "!=") as operator), x, zero)
        when is_zero zero
             && Option.equal Int.equal (integer_width x.Ast.typ) (Some 1) -> (
          match operator with
          | "==" -> { expression with Ast.node = Ast.Unary ("!", x) }
          | _ -> x)
      | Ast.Unary ("!", { node = Ast.Unary ("!", value); _ }) -> value
      | Ast.Unary ("~", value)
        when Option.equal Int.equal (integer_width value.Ast.typ) (Some 1) ->
          { expression with Ast.node = Ast.Unary ("!", value) }
      | Ast.Unary ("~", { node = Ast.Unary ("~", value); _ }) -> value
      | Ast.Unary ("!", { node = Ast.Binary (operator, left, right); _ })
        when List.mem
               [ "=="; "!="; "<"; "<="; ">"; ">=" ]
               operator ~equal:String.equal ->
          let inverse =
            match operator with
            | "==" -> "!="
            | "!=" -> "=="
            | "<" -> ">="
            | "<=" -> ">"
            | ">" -> "<="
            | _ -> "<"
          in
          { expression with Ast.node = Ast.Binary (inverse, left, right) }
      | _ -> expression)
    expression

let rec substitute (variable : Ast.variable) replacement expression =
  map_expression
    (fun expression ->
      match expression.Ast.node with
      | Ast.Var { Ast.typ = Ast.Function _; _ } -> expression
      | Ast.Var candidate when candidate.Ast.id = variable.Ast.id -> replacement
      | _ -> expression)
    expression

let rec substitute_statement (variable : Ast.variable) replacement statement =
  let substitute = substitute variable replacement in
  match statement with
  | Ast.Assign (left, right) -> Ast.Assign (substitute left, substitute right)
  | Ast.Expr expression -> Ast.Expr (substitute expression)
  | Ast.Return None -> statement
  | Ast.Return (Some expression) -> Ast.Return (Some (substitute expression))
  | Ast.If (condition, yes, no) ->
      Ast.If
        ( substitute condition,
          substitute_statements variable replacement yes,
          substitute_statements variable replacement no )
  | Ast.While (condition, body) ->
      Ast.While
        (substitute condition, substitute_statements variable replacement body)
  | Ast.Do_while (body, condition) ->
      Ast.Do_while
        (substitute_statements variable replacement body, substitute condition)
  | Ast.Switch (value, cases, default) ->
      Ast.Switch
        ( substitute value,
          List.map cases ~f:(fun (value, body) ->
              (value, substitute_statements variable replacement body)),
          Option.map default ~f:(substitute_statements variable replacement) )
  | _ -> statement

and substitute_statements variable replacement statements =
  List.map statements ~f:(substitute_statement variable replacement)

let rec side_effect_free expression =
  match expression.Ast.node with
  | Ast.Var _ | Ast.Const _ | Ast.Address _ -> true
  | Ast.Unary (_, x) | Ast.Cast (_, x) -> side_effect_free x
  | Ast.Binary (_, x, y) -> side_effect_free x && side_effect_free y
  | Ast.Conditional (c, x, y) ->
      side_effect_free c && side_effect_free x && side_effect_free y
  | Ast.Aggregate fields ->
      List.for_all fields ~f:(fun (_, value) -> side_effect_free value)
  | Ast.Deref _ | Ast.Field _ | Ast.Index _ | Ast.Call _ | Ast.Machine _
  | Ast.Raw_exp _ ->
      false

let inlineable next value =
  side_effect_free value
  ||
  match (next, value.Ast.node) with
  | (Ast.Expr _ | Ast.Return (Some _)), Ast.Call _ -> true
  | _ -> false

let uses statement (variable : Ast.variable) =
  Set.mem (Decompile_cleanup.used_variables [ statement ]) variable.Ast.id

let rec redefines statement (variable : Ast.variable) =
  match statement with
  | Ast.Assign ({ node = Ast.Var candidate; _ }, _) ->
      candidate.Ast.id = variable.Ast.id
  | Ast.If (_, yes, no) -> redefines_statements (yes @ no) variable
  | Ast.While (_, body) | Ast.Do_while (body, _) ->
      redefines_statements body variable
  | Ast.Switch (_, cases, default) ->
      redefines_statements
        (List.concat_map cases ~f:snd @ Option.value default ~default:[])
        variable
  | _ -> false

and redefines_statements statements variable =
  List.exists statements ~f:(fun statement -> redefines statement variable)

let rec safe_after statements variable dependencies =
  match statements with
  | [] -> true
  | statement :: rest ->
      if uses statement variable then false
      else if redefines statement variable then true
      else if
        Set.exists dependencies ~f:(fun id ->
            redefines statement { variable with Ast.id })
      then false
      else safe_after rest variable dependencies

let inline_statements statements =
  let rec loop previous statements =
    match statements with
    | [] -> []
    | Ast.Assign
        ( { node = Ast.Var (variable : Ast.variable); _ },
          ({ node = Ast.Call _; _ } as call) )
      :: Ast.Return (Some { node = Ast.Var returned; _ })
      :: rest
      when String.equal variable.Ast.name returned.Ast.name ->
        Ast.Return (Some call) :: loop previous rest
    | (Ast.Assign ({ node = Ast.Var (variable : Ast.variable); _ }, value) as
       assignment)
      :: next :: rest
      when inlineable next value && uses next variable
           && (not (redefines next variable))
           && safe_after rest variable
                (Decompile_cleanup.used_variables [ Ast.Expr value ])
           && Set.for_all (Decompile_cleanup.used_variables [ Ast.Expr value ])
                ~f:(fun id ->
                  not (redefines_statements [ next ] { variable with Ast.id }))
      -> (
        match next with
        | Ast.Assign _ | Ast.Expr _ | Ast.Return (Some _) ->
            loop previous (substitute_statement variable value next :: rest)
        | _ -> assignment :: loop (previous @ [ assignment ]) (next :: rest))
    | statement :: rest -> statement :: loop (previous @ [ statement ]) rest
  in
  loop [] statements

let rec optimize_statement statement =
  match statement with
  | Ast.Assign (left, right) ->
      Ast.Assign (simplify_expression left, simplify_expression right)
  | Ast.Expr expression -> Ast.Expr (simplify_expression expression)
  | Ast.Return None -> statement
  | Ast.Return (Some expression) ->
      Ast.Return (Some (simplify_expression expression))
  | Ast.If (condition, yes, no) -> (
      let condition = simplify_expression condition in
      let yes = optimize_statements yes and no = optimize_statements no in
      if is_zero condition && List.length no = 1 then List.hd_exn no
      else if is_one condition && List.length yes = 1 then List.hd_exn yes
      else
        match (yes, no) with
        | ( [ Ast.Assign ({ node = Ast.Var left; _ }, yes_value) ],
            [ Ast.Assign ({ node = Ast.Var right; _ }, no_value) ] )
          when left.Ast.id = right.Ast.id && side_effect_free condition
               && side_effect_free yes_value && side_effect_free no_value ->
            Ast.Assign
              ( Ast.var left,
                {
                  Ast.node = Ast.Conditional (condition, yes_value, no_value);
                  typ = yes_value.Ast.typ;
                } )
        | _ -> Ast.If (condition, yes, no))
  | Ast.While (condition, body) ->
      Ast.While (simplify_expression condition, optimize_statements body)
  | Ast.Do_while (body, condition) ->
      Ast.Do_while (optimize_statements body, simplify_expression condition)
  | Ast.Switch (value, cases, default) ->
      Ast.Switch
        ( simplify_expression value,
          List.map cases ~f:(fun (value, body) ->
              (value, optimize_statements body)),
          Option.map default ~f:optimize_statements )
  | _ -> statement

and optimize_statements statements =
  let statements = List.map statements ~f:optimize_statement in
  inline_statements statements

let rec fixed statements =
  let optimized = optimize_statements statements in
  if Poly.equal optimized statements then optimized else fixed optimized

let statements = fixed

let rec expression_names names expression =
  let names =
    match expression.Ast.node with
    | Ast.Var variable -> Set.add names variable.Ast.name
    | _ -> names
  in
  match expression.Ast.node with
  | Ast.Var _ | Ast.Const _ | Ast.Raw_exp _ -> names
  | Ast.Unary (_, x) | Ast.Cast (_, x) | Ast.Deref x | Ast.Address x ->
      expression_names names x
  | Ast.Binary (_, x, y) -> expression_names (expression_names names x) y
  | Ast.Field (x, _, _) -> expression_names names x
  | Ast.Index (x, index) -> expression_names (expression_names names x) index
  | Ast.Call { target; arguments; _ } ->
      List.fold arguments
        ~init:(expression_names names target)
        ~f:expression_names
  | Ast.Conditional (c, x, y) ->
      expression_names (expression_names (expression_names names c) x) y
  | Ast.Aggregate fields ->
      List.fold fields ~init:names ~f:(fun names (_, value) ->
          expression_names names value)
  | Ast.Machine (_, xs) -> List.fold xs ~init:names ~f:expression_names

let rec statement_names names statement =
  match statement with
  | Ast.Decl _ | Ast.Break | Ast.Continue | Ast.Label _ | Ast.Goto _
  | Ast.Raw_jump _ | Ast.Comment _ ->
      names
  | Ast.Assign (left, right) -> (
      let names = expression_names names right in
      match left.Ast.node with
      | Ast.Var _ -> names
      | _ -> expression_names names left)
  | Ast.Expr expression -> expression_names names expression
  | Ast.Return None -> names
  | Ast.Return (Some expression) -> expression_names names expression
  | Ast.If (condition, yes, no) ->
      statements_names
        (statements_names (expression_names names condition) yes)
        no
  | Ast.While (condition, body) ->
      statements_names (expression_names names condition) body
  | Ast.Do_while (body, condition) ->
      statements_names (expression_names names condition) body
  | Ast.Switch (value, cases, default) ->
      let names = expression_names names value in
      let names =
        List.fold cases ~init:names ~f:(fun names (_, body) ->
            statements_names names body)
      in
      Option.value_map default ~default:names ~f:(statements_names names)

and statements_names names statements =
  List.fold statements ~init:names ~f:statement_names

let remove_frame_saves statements =
  let rec clean statements =
    let used = statements_names String.Set.empty statements in
    List.filter_map statements ~f:(fun statement ->
        match statement with
        | Ast.Assign ({ node = Ast.Var local; _ }, { node = Ast.Var rbp; _ })
          when String.equal rbp.Ast.name "v_RBP"
               && String.is_prefix local.Ast.name ~prefix:"local_"
               && not (Set.mem used local.Ast.name) ->
            None
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

let rec prune_used after statements =
  List.fold_right statements ~init:(after, []) ~f:(fun statement (used, acc) ->
      let statement = prune_nested used statement in
      match statement with
      | Ast.Assign ({ node = Ast.Var variable; _ }, value)
        when side_effect_free value && not (Set.mem used variable.Ast.id) ->
          (used, acc)
      | _ ->
          let statement_uses = Decompile_cleanup.used_variables [ statement ] in
          let used =
            match statement with
            | Ast.Assign ({ node = Ast.Var variable; _ }, _) ->
                Set.remove used variable.Ast.id
            | _ -> used
          in
          let used = Set.union used statement_uses in
          (used, statement :: acc))
  |> snd

and prune_nested after statement =
  match statement with
  | Ast.If (condition, yes, no) ->
      Ast.If (condition, prune_used after yes, prune_used after no)
  | Ast.While (condition, body) ->
      let loop_uses =
        Decompile_cleanup.used_variables [ Ast.While (condition, body) ]
      in
      Ast.While (condition, prune_used (Set.union after loop_uses) body)
  | Ast.Do_while (body, condition) ->
      let loop_uses =
        Decompile_cleanup.used_variables [ Ast.Do_while (body, condition) ]
      in
      Ast.Do_while (prune_used (Set.union after loop_uses) body, condition)
  | Ast.Switch (value, cases, default) ->
      Ast.Switch
        ( value,
          List.map cases ~f:(fun (value, body) ->
              (value, prune_used after body)),
          Option.map default ~f:(prune_used after) )
  | _ -> statement

let rec prune_unused statements =
  let pruned = prune_used Int.Set.empty statements in
  if Poly.equal pruned statements then statements else prune_unused pruned

let program program =
  let functions =
    List.map program.Ast.functions ~f:(fun func ->
        let body = statements func.Ast.body in
        let body = remove_frame_saves body in
        let body = prune_unused body in
        let body = statements body in
        let body = prune_unused body in
        let body = Decompile_cleanup.statements body in
        let used = Decompile_cleanup.used_variables body in
        let locals =
          List.filter func.Ast.locals ~f:(fun local ->
              Set.mem used local.Ast.id)
        in
        { func with Ast.body; locals })
  in
  { program with Ast.functions }
