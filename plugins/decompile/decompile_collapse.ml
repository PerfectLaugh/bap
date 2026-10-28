open Core
module Ast = Decompile_ast

let rec count_gotos statements =
  List.fold statements ~init:String.Map.empty ~f:(fun counts statement ->
      let nested =
        match statement with
        | Ast.If (_, yes, no) -> count_gotos (yes @ no)
        | Ast.While (_, body) | Ast.Do_while (body, _) -> count_gotos body
        | Ast.Switch (_, cases, default) ->
            count_gotos
              (List.concat_map cases ~f:snd @ Option.value default ~default:[])
        | _ -> String.Map.empty
      in
      let counts =
        Map.merge counts nested ~f:(fun ~key:_ -> function
          | `Left count | `Right count -> Some count
          | `Both (left, right) -> Some (left + right))
      in
      match statement with
      | Ast.Goto label ->
          Map.update counts label ~f:(fun count ->
              Option.value count ~default:0 + 1)
      | _ -> counts)

let regions statements =
  let rec collect current acc = function
    | [] ->
        Option.map current ~f:(fun (label, body) -> (label, List.rev body))
        |> Option.to_list
        |> fun region -> region @ acc
    | Ast.Label label :: rest ->
        let current =
          Option.map current ~f:(fun (label, body) -> (label, List.rev body))
        in
        collect (Some (label, [])) (Option.to_list current @ acc) rest
    | statement :: rest ->
        let current =
          Option.map current ~f:(fun (label, body) ->
              (label, statement :: body))
        in
        collect current acc rest
  in
  collect None [] statements

let drop_region statements label =
  let rec drop skipping = function
    | [] -> []
    | Ast.Label other :: rest when String.equal label other -> drop true rest
    | (Ast.Label _ as marker) :: rest when skipping -> marker :: drop false rest
    | _ :: rest when skipping -> drop true rest
    | statements -> statements
  in
  drop false statements

let rec replace_gotos label body statements =
  List.concat_map statements ~f:(fun statement ->
      match statement with
      | Ast.Goto target when String.equal target label -> body
      | Ast.If (condition, yes, no) ->
          [
            Ast.If
              ( condition,
                replace_gotos label body yes,
                replace_gotos label body no );
          ]
      | Ast.While (condition, loop) ->
          [ Ast.While (condition, replace_gotos label body loop) ]
      | Ast.Do_while (loop, condition) ->
          [ Ast.Do_while (replace_gotos label body loop, condition) ]
      | Ast.Switch (value, cases, default) ->
          [
            Ast.Switch
              ( value,
                List.map cases ~f:(fun (value, body) ->
                    (value, replace_gotos label body body)),
                Option.map default ~f:(replace_gotos label body) );
          ]
      | statement -> [ statement ])

let region_position statements label =
  List.find_mapi statements ~f:(fun index statement ->
      match statement with
      | Ast.Label candidate when String.equal candidate label -> Some index
      | _ -> None)

let score (cfg : Decompile_cfg.t) label =
  match
    Set.find (Decompile_cfg.nodes cfg) ~f:(fun tid ->
        String.equal (Decompile_cfg.label tid) label)
  with
  | None -> (1, Int.max_value, Int.max_value)
  | Some tid ->
      let terminal = if Decompile_cfg.is_exit cfg tid then 0 else 1 in
      let depth =
        Set.count (Decompile_cfg.nodes cfg) ~f:(fun other ->
            Decompile_cfg.dominates cfg other tid)
      in
      (terminal, depth, List.length (Decompile_cfg.predecessors cfg tid))

let rec inline cfg statements =
  let counts = count_gotos statements in
  let regions = regions statements in
  let rec visit position = function
    | [] -> []
    | Ast.Goto label :: rest ->
        let candidates = visit (position + 1) rest in
        if not (List.is_empty rest) then candidates
        else
          let target = region_position statements label in
          if
            Option.exists target ~f:(fun target -> target > position)
            && Option.equal Int.equal (Map.find counts label) (Some 1)
          then
            match List.Assoc.find regions label ~equal:String.equal with
            | Some body -> (label, body, score cfg label) :: candidates
            | None -> candidates
          else candidates
    | _ :: rest -> visit (position + 1) rest
  in
  match
    List.min_elt (visit 0 statements)
      ~compare:(fun (_, _, left) (_, _, right) -> Poly.compare left right)
  with
  | None -> statements
  | Some (label, body, _) ->
      let statements = replace_gotos label body statements in
      inline cfg (drop_region statements label)

let rec map_nested f statements =
  List.map statements ~f:(fun statement ->
      match statement with
      | Ast.If (condition, yes, no) -> Ast.If (condition, f yes, f no)
      | Ast.While (condition, body) -> Ast.While (condition, f body)
      | Ast.Do_while (body, condition) -> Ast.Do_while (f body, condition)
      | Ast.Switch (value, cases, default) ->
          Ast.Switch
            ( value,
              List.map cases ~f:(fun (value, body) -> (value, f body)),
              Option.map default ~f )
      | statement -> statement)

let rec collapse cfg statements =
  let next = inline cfg statements |> map_nested (collapse cfg) in
  if Poly.equal next statements then next else collapse cfg next

let structure cfg ~block ~edge ~call ~condition =
  Decompile_structure.structure cfg ~block ~edge ~call ~condition
  |> collapse cfg
