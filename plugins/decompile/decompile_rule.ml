open Core

type 'a t = { name : string; operations : string list; apply : 'a -> 'a option }
type 'a summary = { changes : int; applications : (string * int) list }

let rule ?(operations = []) name apply = { name; operations; apply }

let run ?(limit = 64) ~key ~equal ~map rules initial =
  if limit < 1 then invalid_arg "Decompile_rule.run: limit must be positive";
  let indexed =
    List.concat_map rules ~f:(fun rule ->
        List.map rule.operations ~f:(fun operation -> (operation, rule)))
  in
  let generic =
    List.filter rules ~f:(fun rule -> List.is_empty rule.operations)
  in
  let counts = Hashtbl.create (module String) in
  let rec one expression =
    let operation = key expression in
    let candidates =
      List.filter_map indexed ~f:(fun (name, rule) ->
          if String.equal operation name then Some rule else None)
      |> fun specific -> specific @ generic
    in
    List.find_map candidates ~f:(fun rule ->
        match rule.apply expression with
        | None -> None
        | Some replacement when equal expression replacement -> None
        | Some replacement ->
            Hashtbl.incr counts rule.name;
            Some replacement)
  in
  let rec fixed expression iterations =
    let changed = ref false in
    let next =
      map
        (fun expression ->
          match one expression with
          | None -> expression
          | Some replacement ->
              changed := true;
              replacement)
        expression
    in
    if not !changed then (next, iterations)
    else if iterations + 1 >= limit then (next, iterations + 1)
    else fixed next (iterations + 1)
  in
  let result, iterations = fixed initial 0 in
  let applications =
    List.map rules ~f:(fun rule ->
        (rule.name, Hashtbl.find_or_add counts rule.name ~default:(fun () -> 0)))
    |> List.filter ~f:(fun (_, count) -> count > 0)
  in
  (result, { changes = iterations; applications })
