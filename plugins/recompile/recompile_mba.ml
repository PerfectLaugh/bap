open Core
open Bap.Std
open Result.Monad_infix

let default_max_iterations = 32
let default_max_rewrites = 10000

type state = { mutable remaining : int }

let zero exp =
  match Type.infer exp with
  | Ok (Type.Imm width) -> Bil.int (Word.zero width)
  | _ -> assert false

let one exp =
  match Type.infer exp with
  | Ok (Type.Imm width) -> Bil.int (Word.one width)
  | _ -> assert false

let is_zero = function Bil.Int word -> Word.is_zero word | _ -> false
let is_one = function Bil.Int word -> Word.is_one word | _ -> false

let is_ones = function
  | Bil.Int word -> Word.equal word (Word.ones (Word.bitwidth word))
  | _ -> false

let commutative = function
  | Bil.PLUS | Bil.TIMES | Bil.AND | Bil.OR | Bil.XOR -> true
  | _ -> false

let rec flatten operation exp =
  match exp with
  | Bil.BinOp (op, left, right) when Poly.(op = operation) ->
      flatten operation left @ flatten operation right
  | _ -> [ exp ]

let rebuild operation operands =
  List.reduce_balanced operands ~f:(fun left right ->
      Bil.BinOp (operation, left, right))
  |> Option.value_exn

let normalize operation left right =
  let operands =
    flatten operation (Bil.BinOp (operation, left, right))
    |> List.sort ~compare:Exp.compare
  in
  rebuild operation operands

let is_and x y = function
  | Bil.BinOp (Bil.AND, left, right) ->
      (Exp.equal left x && Exp.equal right y)
      || (Exp.equal left y && Exp.equal right x)
  | _ -> false

let twice_and x y = function
  | Bil.BinOp (Bil.PLUS, left, right) -> is_and x y left && is_and x y right
  | Bil.BinOp (Bil.TIMES, Bil.Int factor, value)
  | Bil.BinOp (Bil.TIMES, value, Bil.Int factor) ->
      Word.equal factor (Word.of_int ~width:(Word.bitwidth factor) 2)
      && is_and x y value
  | _ -> false

let and_ x y = Bil.BinOp (Bil.AND, x, y)
let xor x y = Bil.BinOp (Bil.XOR, x, y)
let or_ x y = Bil.BinOp (Bil.OR, x, y)
let plus x y = Bil.BinOp (Bil.PLUS, x, y)

let shift_add x amount =
  match (Type.infer x, Word.to_int amount) with
  | Ok (Type.Imm width), Ok shift when shift >= 0 && shift < width ->
      let coefficient = Int64.(shift_left one shift + one) in
      Some
        (Bil.BinOp (Bil.TIMES, x, Bil.int (Word.of_int64 ~width coefficient)))
  | _ -> None

let mba = function
  | Bil.BinOp (Bil.PLUS, x, Bil.BinOp (Bil.LSHIFT, y, Bil.Int amount))
    when Exp.equal x y ->
      shift_add x amount
  | Bil.BinOp (Bil.PLUS, Bil.BinOp (Bil.LSHIFT, y, Bil.Int amount), x)
    when Exp.equal x y ->
      shift_add x amount
  | Bil.BinOp (Bil.PLUS, Bil.BinOp (Bil.XOR, x, y), rest)
    when twice_and x y rest ->
      Some (plus x y)
  | Bil.BinOp (Bil.PLUS, Bil.BinOp (Bil.XOR, x, y), Bil.BinOp (Bil.AND, a, b))
    when (Exp.equal x a && Exp.equal y b) || (Exp.equal x b && Exp.equal y a) ->
      Some (or_ x y)
  | Bil.BinOp (Bil.PLUS, Bil.BinOp (Bil.OR, x, y), Bil.BinOp (Bil.AND, a, b))
    when (Exp.equal x a && Exp.equal y b) || (Exp.equal x b && Exp.equal y a) ->
      Some (plus x y)
  | Bil.BinOp (Bil.MINUS, Bil.BinOp (Bil.OR, x, y), Bil.BinOp (Bil.AND, a, b))
    when (Exp.equal x a && Exp.equal y b) || (Exp.equal x b && Exp.equal y a) ->
      Some (xor x y)
  | Bil.BinOp (Bil.MINUS, Bil.BinOp (Bil.OR, x, y), Bil.BinOp (Bil.XOR, a, b))
    when (Exp.equal x a && Exp.equal y b) || (Exp.equal x b && Exp.equal y a) ->
      Some (and_ x y)
  | Bil.BinOp (Bil.MINUS, Bil.BinOp (Bil.PLUS, x, y), rest)
    when twice_and x y rest ->
      Some (xor x y)
  | _ -> None

let local exp =
  let simplified =
    match exp with
    | Bil.BinOp (op, left, right) -> (
        match mba exp with
        | Some _ as result -> result
        | None -> (
            match op with
            | Bil.PLUS when is_zero left -> Some right
            | Bil.PLUS when is_zero right -> Some left
            | Bil.MINUS when is_zero right -> Some left
            | Bil.MINUS when Exp.equal left right -> Some (zero left)
            | Bil.TIMES when is_zero left || is_zero right -> Some (zero left)
            | Bil.TIMES when is_one left -> Some right
            | Bil.TIMES when is_one right -> Some left
            | Bil.DIVIDE when is_one right -> Some left
            | (Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT) when is_zero right ->
                Some left
            | Bil.AND when is_zero left || is_zero right -> Some (zero left)
            | Bil.AND when is_ones left -> Some right
            | Bil.AND when is_ones right -> Some left
            | (Bil.AND | Bil.OR) when Exp.equal left right -> Some left
            | Bil.OR when is_zero left -> Some right
            | Bil.OR when is_zero right -> Some left
            | Bil.OR when is_ones left -> Some left
            | Bil.OR when is_ones right -> Some right
            | Bil.XOR when is_zero left -> Some right
            | Bil.XOR when is_zero right -> Some left
            | Bil.XOR when Exp.equal left right -> Some (zero left)
            | (Bil.EQ | Bil.LE | Bil.SLE) when Exp.equal left right ->
                Some (one exp)
            | (Bil.NEQ | Bil.LT | Bil.SLT) when Exp.equal left right ->
                Some (zero exp)
            | _ -> None))
    | Bil.UnOp (Bil.NEG, Bil.UnOp (Bil.NEG, value))
    | Bil.UnOp (Bil.NOT, Bil.UnOp (Bil.NOT, value)) ->
        Some value
    | Bil.Ite (condition, yes, no) when is_one condition -> Some yes
    | Bil.Ite (condition, yes, no) when is_zero condition -> Some no
    | Bil.Ite (_, yes, no) when Exp.equal yes no -> Some yes
    | _ -> None
  in
  match simplified with
  | Some value -> value
  | None -> (
      match exp with
      | Bil.BinOp (op, left, right) when commutative op ->
          normalize op left right
      | _ -> exp)

let rec is_pure = function
  | Bil.Var _ | Bil.Int _ -> true
  | Bil.Load _ | Bil.Store _ | Bil.Let _ | Bil.Unknown _ -> false
  | Bil.BinOp (_, left, right) | Bil.Concat (left, right) ->
      is_pure left && is_pure right
  | Bil.UnOp (_, value) | Bil.Cast (_, _, value) | Bil.Extract (_, _, value) ->
      is_pure value
  | Bil.Ite (condition, yes, no) ->
      is_pure condition && is_pure yes && is_pure no

let rec rewrite state exp =
  let exp =
    match exp with
    | Bil.BinOp (op, left, right) ->
        Bil.BinOp (op, rewrite state left, rewrite state right)
    | Bil.UnOp (op, value) -> Bil.UnOp (op, rewrite state value)
    | Bil.Cast (cast, width, value) ->
        Bil.Cast (cast, width, rewrite state value)
    | Bil.Let (var, value, body) ->
        Bil.Let (var, rewrite state value, rewrite state body)
    | Bil.Load (mem, addr, endian, size) ->
        Bil.Load (rewrite state mem, rewrite state addr, endian, size)
    | Bil.Store (mem, addr, value, endian, size) ->
        Bil.Store
          ( rewrite state mem,
            rewrite state addr,
            rewrite state value,
            endian,
            size )
    | Bil.Ite (condition, yes, no) ->
        Bil.Ite (rewrite state condition, rewrite state yes, rewrite state no)
    | Bil.Extract (hi, lo, value) -> Bil.Extract (hi, lo, rewrite state value)
    | Bil.Concat (left, right) ->
        Bil.Concat (rewrite state left, rewrite state right)
    | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> exp
  in
  let after = if is_pure exp then Exp.fold_consts (local exp) else exp in
  if Exp.equal exp after then exp
  else if state.remaining = 0 then failwith "rewrite budget exhausted"
  else (
    state.remaining <- state.remaining - 1;
    after)

let simplify_exp ?(max_iterations = default_max_iterations)
    ?(max_rewrites = default_max_rewrites) before =
  if max_iterations < 0 || max_rewrites < 0 then
    Or_error.error_string
      "MBA iteration and rewrite budgets must be non-negative"
  else
    try
      let state = { remaining = max_rewrites } in
      let rec loop iterations current =
        let after = rewrite state current in
        if Exp.equal current after then Ok after
        else if iterations = max_iterations then
          Or_error.error_string "MBA iteration budget exhausted"
        else loop (iterations + 1) after
      in
      loop 0 before
    with Failure message -> Or_error.error_string message

let simplify_exp_with ?max_iterations ?max_rewrites ~validate before =
  simplify_exp ?max_iterations ?max_rewrites before >>= fun after ->
  if Exp.equal before after then Ok after
  else
    match validate before after with
    | Ok () -> Ok after
    | Error message ->
        Or_error.error_string
          (Format.asprintf
             "Lean rejected MBA rewrite: %s@.original: %a@.optimized: %a"
             message Exp.pp before Exp.pp after)

let simplify_exp_checked =
  simplify_exp_with ~validate:Bap_bil_plugin.Bil_lean.validate_exp_exact

let map_term ?max_iterations ?max_rewrites ~validate kind term =
  let failed = ref None in
  let term =
    kind term ~f:(fun before ->
        if Option.is_some !failed then before
        else
          match
            simplify_exp_with ?max_iterations ?max_rewrites ~validate before
          with
          | Ok after -> after
          | Error error ->
              failed := Some error;
              before)
  in
  match !failed with
  | None -> Ok term
  | Some error ->
      Or_error.errorf "MBA optimization failed at %s: %s"
        (Tid.to_string (Term.tid term))
        (Error.to_string_hum error)

type facts = {
  mutable expressions : Bil.exp Var.Map.t;
  mutable dependencies : Var.Set.t Var.Map.t;
}

let empty_facts () =
  { expressions = Var.Map.empty; dependencies = Var.Map.empty }

let clear facts =
  facts.expressions <- Var.Map.empty;
  facts.dependencies <- Var.Map.empty

let kill facts var =
  facts.expressions <- Map.remove facts.expressions var;
  Map.find facts.dependencies var
  |> Option.value ~default:Var.Set.empty
  |> Set.iter ~f:(fun dependent ->
      facts.expressions <- Map.remove facts.expressions dependent);
  facts.dependencies <-
    Map.remove facts.dependencies var
    |> Map.map ~f:(fun deps -> Set.remove deps var)

let rec depth = function
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> 1
  | Bil.BinOp (_, left, right) | Bil.Concat (left, right) ->
      1 + max (depth left) (depth right)
  | Bil.UnOp (_, value) | Bil.Cast (_, _, value) | Bil.Extract (_, _, value) ->
      1 + depth value
  | Bil.Load (mem, addr, _, _) -> 1 + max (depth mem) (depth addr)
  | Bil.Store (mem, addr, value, _, _) ->
      1 + max (depth mem) (max (depth addr) (depth value))
  | Bil.Let (_, value, body) -> 1 + max (depth value) (depth body)
  | Bil.Ite (condition, yes, no) ->
      1 + max (depth condition) (max (depth yes) (depth no))

let propagatable facts var exp =
  Var.is_virtual var && is_pure exp
  && depth exp <= 3
  && Map.length facts.expressions < 32
  &&
  let free = Exp.free_vars exp in
  Set.length free = 1 && not (Set.mem free var)

let define facts var exp =
  kill facts var;
  if propagatable facts var exp then (
    let source = Set.choose_exn (Exp.free_vars exp) in
    facts.expressions <- Map.set facts.expressions ~key:var ~data:exp;
    facts.dependencies <-
      Map.update facts.dependencies source ~f:(fun deps ->
          Set.add (Option.value deps ~default:Var.Set.empty) var))

let substitute facts exp =
  Map.fold facts.expressions ~init:exp ~f:(fun ~key ~data exp ->
      Exp.substitute (Bil.Var key) data exp)

let propagate_blk ~validate blk =
  let facts = empty_facts () and failed = ref None in
  let apply before =
    if Option.is_some !failed then before
    else
      let after = substitute facts before in
      if Exp.equal before after then after
      else
        let used = Exp.free_vars before in
        let assumptions =
          Map.filter_keys facts.expressions ~f:(fun var -> Set.mem used var)
          |> Map.to_alist
        in
        match validate ~assumptions before after with
        | Ok () -> after
        | Error message ->
            failed := Some message;
            before
  in
  let def def =
    if Option.is_some !failed then def
    else
      let rhs = apply (Def.rhs def) in
      let lhs = Def.lhs def in
      define facts lhs rhs;
      Def.with_rhs def rhs
  in
  let jmp jmp =
    let after = Jmp.map_exp jmp ~f:apply in
    (match Jmp.kind jmp with Call _ -> clear facts | _ -> ());
    after
  in
  let blk = Blk.map_elts ~def ~jmp blk in
  match !failed with
  | None -> Ok blk
  | Some message ->
      Or_error.errorf "Lean rejected MBA copy propagation at %s: %s"
        (Tid.to_string (Term.tid blk))
        message

let accept_propagation ~assumptions:_ _ _ = Ok ()

let simplify_blk_with ?max_iterations ?max_rewrites ~validate
    ?(validate_propagation = fun ~assumptions:_ -> validate) blk =
  propagate_blk ~validate:validate_propagation blk >>= fun blk ->
  map_term ?max_iterations ?max_rewrites ~validate
    (fun blk ~f -> Blk.map_exp blk ~f)
    blk

let simplify_blk =
  simplify_blk_with
    ~validate:(fun _ _ -> Ok ())
    ~validate_propagation:accept_propagation

let simplify_blk_checked =
  simplify_blk_with ~validate:Bap_bil_plugin.Bil_lean.validate_exp_exact
    ~validate_propagation:Bap_bil_plugin.Bil_lean.validate_assumptions

let simplify_with ?max_iterations ?max_rewrites ~validate ?validate_propagation
    sub =
  Term.enum blk_t sub |> Seq.to_list
  |> List.fold ~init:(Ok []) ~f:(fun result blk ->
      result >>= fun blks ->
      simplify_blk_with ?max_iterations ?max_rewrites ~validate
        ?validate_propagation blk
      >>| fun blk -> blk :: blks)
  >>| fun blks ->
  Term.map blk_t sub ~f:(fun blk ->
      List.find_exn blks ~f:(fun candidate ->
          Tid.equal (Term.tid blk) (Term.tid candidate)))

let simplify =
  simplify_with
    ~validate:(fun _ _ -> Ok ())
    ~validate_propagation:accept_propagation

let simplify_checked =
  simplify_with ~validate:Bap_bil_plugin.Bil_lean.validate_exp_exact
    ~validate_propagation:Bap_bil_plugin.Bil_lean.validate_assumptions
