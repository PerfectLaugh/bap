open Core
open Bap.Std
module Ast = Decompile_ast

let rec declaration typ name =
  let open Ast in
  match typ with
  | Unknown 0 -> sprintf "void %s" name
  | Memory -> sprintf "bir_mem_t %s" name
  | Unknown bits -> sprintf "bir_unknown%d_t %s" bits name
  | Bool -> sprintf "_Bool %s" name
  | Int (1, _) -> sprintf "_Bool %s" name
  | Int (bits, Signed) -> sprintf "int%d_t %s" bits name
  | Int (bits, _) -> sprintf "uint%d_t %s" bits name
  | Float 32 -> sprintf "float %s" name
  | Float 64 -> sprintf "double %s" name
  | Float 128 -> sprintf "long double %s" name
  | Float bits -> sprintf "bir_float%d_t %s" bits name
  | Structure structure -> sprintf "struct %s %s" structure name
  | Pointer (Function signature) ->
      sprintf "%s (*%s)(%s)"
        (declaration signature.return "" |> String.strip)
        name
        (parameters signature.params signature.variadic)
  | Pointer (Array _ as inner) -> declaration inner (sprintf "(*%s)" name)
  | Pointer inner -> declaration inner (sprintf "*%s" name)
  | Array (element, Some size) ->
      declaration element (sprintf "%s[%d]" name size)
  | Array (element, None) -> declaration element (sprintf "%s[]" name)
  | Function signature ->
      sprintf "%s %s(%s)"
        (declaration signature.return "" |> String.strip)
        name
        (parameters signature.params signature.variadic)

and parameters params variadic =
  let params = List.map params ~f:(fun (name, typ) -> declaration typ name) in
  let params = if variadic then params @ [ "..." ] else params in
  match params with [] -> "void" | params -> String.concat ~sep:", " params

let precedence (node : Ast.expr) =
  match node with
  | Ast.Conditional _ -> 2
  | Ast.Binary (("||" | "&&"), _, _) -> 3
  | Ast.Binary (("|" | "^" | "&"), _, _) -> 5
  | Ast.Binary (("==" | "!="), _, _) -> 6
  | Ast.Binary (("<" | ">" | "<=" | ">="), _, _) -> 7
  | Ast.Binary (("<<" | ">>"), _, _) -> 8
  | Ast.Binary (("+" | "-"), _, _) -> 9
  | Ast.Binary (("*" | "/" | "%"), _, _) -> 10
  | Ast.Unary _ | Ast.Cast _ | Ast.Deref _ | Ast.Address _ -> 11
  | _ -> 12

let rec expression ppf (expr : Ast.expression) =
  let parenthesize parent ppf (current : Ast.expression) =
    if precedence current.Ast.node < parent then
      Format.fprintf ppf "(%a)" expression current
    else expression ppf current
  in
  match expr.Ast.node with
  | Ast.Var variable -> Format.pp_print_string ppf variable.name
  | Ast.Const value -> (
      match Word.to_int value with
      | Ok small when small >= 0 && small < 1000 ->
          Format.fprintf ppf "%d" small
      | _ -> Format.fprintf ppf "0x%s" (Word.string_of_value ~hex:true value))
  | Ast.Unary (operator, operand) ->
      Format.fprintf ppf "%s%a" operator (parenthesize 11) operand
  | Ast.Binary (operator, left, right) ->
      let level = precedence expr.node in
      Format.fprintf ppf "%a %s %a" (parenthesize level) left operator
        (parenthesize (level + 1))
        right
  | Ast.Cast (typ, operand) ->
      Format.fprintf ppf "(%s)%a"
        (declaration typ "" |> String.strip)
        (parenthesize 11) operand
  | Ast.Deref pointer -> Format.fprintf ppf "*%a" (parenthesize 11) pointer
  | Ast.Address operand -> Format.fprintf ppf "&%a" (parenthesize 11) operand
  | Ast.Field (base, field, _) ->
      let operator =
        match base.Ast.typ with
        | Ast.Pointer (Ast.Structure _) -> "->"
        | _ -> "."
      in
      Format.fprintf ppf "%a%s%s" (parenthesize 12) base operator field
  | Ast.Index (base, index) ->
      Format.fprintf ppf "%a[%a]" (parenthesize 12) base expression index
  | Ast.Call { target; arguments; _ } ->
      Format.fprintf ppf "%a(%a)" (parenthesize 12) target arguments_pp
        arguments
  | Ast.Conditional (condition, yes, no) ->
      Format.fprintf ppf "%a ? %a : %a" (parenthesize 3) condition expression
        yes (parenthesize 2) no
  | Ast.Aggregate fields ->
      Format.fprintf ppf "{ ";
      List.iteri fields ~f:(fun index (field, value) ->
          if index > 0 then Format.fprintf ppf ", ";
          Format.fprintf ppf ".%s = %a" field expression value);
      Format.fprintf ppf " }"
  | Ast.Machine (name, arguments) ->
      Format.fprintf ppf "%s(%a)" name arguments_pp arguments
  | Ast.Raw_exp exp -> Format.fprintf ppf "bir_raw(%S)" (Exp.to_string exp)

and arguments_pp ppf arguments =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
    expression ppf arguments

let rec statement ppf indent stmt =
  let open Ast in
  let start () = Format.fprintf ppf "%s" (String.make indent ' ') in
  match stmt with
  | Decl variable ->
      start ();
      Format.fprintf ppf "%s;" (declaration variable.typ variable.name)
  | Assign (left, right) ->
      start ();
      Format.fprintf ppf "%a = %a;" expression left expression right
  | Expr expression' ->
      start ();
      Format.fprintf ppf "%a;" expression expression'
  | Return None ->
      start ();
      Format.pp_print_string ppf "return;"
  | Return (Some value) ->
      start ();
      Format.fprintf ppf "return %a;" expression value
  | If (condition, yes, []) ->
      start ();
      Format.fprintf ppf "if (%a) {@\n" expression condition;
      statements ppf (indent + 2) yes;
      Format.fprintf ppf "%s}" (String.make indent ' ')
  | If (condition, yes, no) ->
      start ();
      Format.fprintf ppf "if (%a) {@\n" expression condition;
      statements ppf (indent + 2) yes;
      Format.fprintf ppf "%s} else {@\n" (String.make indent ' ');
      statements ppf (indent + 2) no;
      Format.fprintf ppf "%s}" (String.make indent ' ')
  | While (condition, body) ->
      start ();
      Format.fprintf ppf "while (%a) {@\n" expression condition;
      statements ppf (indent + 2) body;
      Format.fprintf ppf "%s}" (String.make indent ' ')
  | Do_while (body, condition) ->
      start ();
      Format.fprintf ppf "do {@\n";
      statements ppf (indent + 2) body;
      Format.fprintf ppf "%s} while (%a);" (String.make indent ' ') expression
        condition
  | Switch (value, cases, default) ->
      start ();
      Format.fprintf ppf "switch (%a) {@\n" expression value;
      List.iter cases ~f:(fun (value, body) ->
          Format.fprintf ppf "%scase 0x%s:@\n"
            (String.make (indent + 2) ' ')
            (Word.string_of_value ~hex:true value);
          statements ppf (indent + 4) body);
      Option.iter default ~f:(fun body ->
          Format.fprintf ppf "%sdefault:@\n" (String.make (indent + 2) ' ');
          statements ppf (indent + 4) body);
      Format.fprintf ppf "%s}" (String.make indent ' ')
  | Break ->
      start ();
      Format.pp_print_string ppf "break;"
  | Continue ->
      start ();
      Format.pp_print_string ppf "continue;"
  | Label label -> Format.fprintf ppf "%s:" label
  | Goto label ->
      start ();
      Format.fprintf ppf "goto %s;" label
  | Raw_jump jump ->
      start ();
      Format.fprintf ppf "bir_raw_jump(/* %S */);" (Jmp.to_string jump)
  | Comment comment ->
      start ();
      Format.fprintf ppf "/* %s */" comment

and statements ppf indent statements =
  List.iter statements ~f:(fun stmt ->
      statement ppf indent stmt;
      Format.fprintf ppf "@\n")

let pp ppf program =
  Format.fprintf ppf
    "/* Recovered C pseudocode; bir_* operations require machine support. */@\n";
  List.iter program.Ast.structures ~f:(fun structure ->
      Format.fprintf ppf "struct %s {@\n" structure.name;
      List.iter structure.fields ~f:(fun (name, offset, typ) ->
          Format.fprintf ppf "  %s; /* +0x%x */@\n" (declaration typ name)
            offset);
      Format.fprintf ppf "};@\n@\n");
  List.iter program.functions ~f:(fun func ->
      if func.Ast.external_ then
        Format.fprintf ppf "%s;@\n"
          (declaration (Ast.Function func.signature) func.name));
  if List.exists program.functions ~f:(fun func -> func.Ast.external_) then
    Format.fprintf ppf "@\n";
  List.iter program.functions ~f:(fun func ->
      if not func.Ast.external_ then begin
        Format.fprintf ppf "%s {@\n"
          (declaration (Ast.Function func.signature) func.name);
        List.iter func.locals ~f:(fun local ->
            Format.fprintf ppf "  %s;@\n" (declaration local.typ local.name));
        if not (List.is_empty func.locals) then Format.fprintf ppf "@\n";
        statements ppf 2 func.body;
        Format.fprintf ppf "}@\n@\n"
      end)

let to_string program = Format.asprintf "%a" pp program
