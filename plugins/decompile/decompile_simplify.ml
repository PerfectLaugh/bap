open Core
open Bap.Std

let is_zero = function Bil.Int value -> Word.is_zero value | _ -> false
let is_one = function Bil.Int value -> Word.is_one value | _ -> false

let is_ones = function
  | Bil.Int value -> Word.equal value (Word.ones (Word.bitwidth value))
  | _ -> false

let width exp =
  match Type.infer exp with Ok (Type.Imm bits) -> Some bits | _ -> None

let apply_binop op x y =
  match (x, y) with
  | Bil.Int x, Bil.Int y -> (
      try Some (Bil.Int (Bil.Apply.binop op x y)) with _ -> None)
  | _ -> None

let signed_less a b =
  let msb = function
    | Bil.Extract (hi, lo, exp) when hi = lo -> Some (hi, exp)
    | _ -> None
  in
  let overflow_dnf hi result left right overflow =
    let rec terms = function
      | Bil.BinOp (OR, x, y) -> terms x @ terms y
      | exp -> [ exp ]
    in
    let rec factors = function
      | Bil.BinOp (AND, x, y) -> factors x @ factors y
      | exp -> [ exp ]
    in
    let literal exp =
      let negative, exp =
        match exp with Bil.UnOp (NOT, x) -> (true, x) | _ -> (false, exp)
      in
      match msb exp with
      | Some (bit, exp) when bit = hi -> Some (negative, exp)
      | _ -> None
    in
    let literals term = Option.all (List.map (factors term) ~f:literal) in
    let same_sign exp expected =
      Exp.equal exp expected
      ||
      match expected with
      | Bil.Extract (bit, 0, inner) when bit = hi -> Exp.equal exp inner
      | _ -> false
    in
    let has negative exp =
      List.exists ~f:(fun (n, e) -> Bool.equal negative n && same_sign e exp)
    in
    let right_sign literals =
      List.find_map literals ~f:(fun (negative, exp) ->
          if
            same_sign exp right
            ||
            match exp with
            | Bil.UnOp (NOT, value) -> same_sign value right
            | _ -> false
          then Some negative
          else None)
    in
    let valid first second =
      List.length first = 3
      && List.length second = 3
      && has true result first && has false result second
      && has false left first && has true left second
      &&
      match (right_sign first, right_sign second) with
      | Some x, Some y -> not (Bool.equal x y)
      | _ -> false
    in
    match List.map (terms overflow) ~f:literals with
    | [ Some first; Some second ] -> valid first second || valid second first
    | _ -> false
  in
  let check sf overflow =
    match msb sf with
    | Some (hi, result) -> (
        let hi', overflow =
          match msb overflow with
          | Some (hi, overflow) -> (hi, overflow)
          | None -> (hi, overflow)
        in
        if hi <> hi' then None
        else
          match result with
          | Bil.BinOp (MINUS, left, right) -> (
              match overflow with
              | Bil.BinOp
                  (AND, Bil.BinOp (XOR, x, y), Bil.BinOp (XOR, x', result'))
                when Exp.equal x x' && Exp.equal result result'
                     && Exp.equal x left && Exp.equal y right ->
                  Some (hi, left, right)
              | _ when overflow_dnf hi result left right overflow ->
                  Some (hi, left, right)
              | _ -> None)
          | _ -> None)
    | _ -> None
  in
  match check a b with Some _ as result -> result | None -> check b a

let as_subtraction exp =
  let rec terms = function
    | Bil.BinOp (PLUS, x, y) -> terms x @ terms y
    | exp -> [ exp ]
  in
  let rec split ones complements rest = function
    | [] -> (
        match (ones, complements, rest) with
        | [ _ ], [ y ], [ x ] -> Some (x, y)
        | _ -> None)
    | Bil.Int one :: xs when Word.is_one one ->
        split (one :: ones) complements rest xs
    | Bil.UnOp (NOT, y) :: xs -> split ones (y :: complements) rest xs
    | x :: xs -> split ones complements (x :: rest) xs
  in
  split [] [] [] (terms exp)

let rec simplify exp =
  let simplified = simplify_descendant exp in
  if Exp.equal exp simplified then exp else simplify simplified

and simplify_descendant exp =
  let exp = simplify_children exp in
  match exp with
  | Bil.BinOp (((EQ | NEQ) as op), a, b) when Option.is_some (signed_less a b)
    -> (
      let hi, x, y = Option.value_exn (signed_less a b) in
      match
        ( Option.equal Int.equal (width x) (Some (hi + 1)),
          Option.equal Int.equal (width y) (Some (hi + 1)) )
      with
      | true, true -> (
          match op with
          | EQ -> Bil.UnOp (NOT, Bil.BinOp (SLT, x, y))
          | _ -> Bil.BinOp (SLT, x, y))
      | _ -> exp)
  | Bil.BinOp (op, x, y) -> (
      match apply_binop op x y with
      | Some value -> value
      | None -> (
          match (op, x, y) with
          | (EQ | NEQ), Bil.Cast (_, _, value), Bil.Int zero
            when Word.is_zero zero
                 && Option.equal Int.equal (width value) (Some 1) ->
              if Poly.equal op EQ then Bil.UnOp (NOT, value) else value
          | (EQ | NEQ), Bil.Int zero, Bil.Cast (_, _, value)
            when Word.is_zero zero
                 && Option.equal Int.equal (width value) (Some 1) ->
              if Poly.equal op EQ then Bil.UnOp (NOT, value) else value
          | (EQ | NEQ), Bil.Extract (hi, lo, value), Bil.Int zero
            when hi = lo && Word.is_zero zero
                 && Option.equal Int.equal (width value) (Some (hi + 1)) ->
              let zero = Bil.Int (Word.zero (hi + 1)) in
              if Poly.equal op EQ then Bil.BinOp (SLE, zero, value)
              else Bil.BinOp (SLT, value, zero)
          | (EQ | NEQ), Bil.Int zero, Bil.Extract (hi, lo, value)
            when hi = lo && Word.is_zero zero
                 && Option.equal Int.equal (width value) (Some (hi + 1)) ->
              let zero = Bil.Int (Word.zero (hi + 1)) in
              if Poly.equal op EQ then Bil.BinOp (SLE, zero, value)
              else Bil.BinOp (SLT, value, zero)
          | (EQ | NEQ), Bil.BinOp (MINUS, left, right), Bil.Int zero
            when Word.is_zero zero ->
              Bil.BinOp (op, left, right)
          | (EQ | NEQ), Bil.Int zero, Bil.BinOp (MINUS, left, right)
            when Word.is_zero zero ->
              Bil.BinOp (op, left, right)
          | PLUS, x, y when is_zero x || is_zero y -> if is_zero x then y else x
          | PLUS, _, _ when Option.is_some (as_subtraction exp) ->
              let x, y = Option.value_exn (as_subtraction exp) in
              Bil.BinOp (MINUS, x, y)
          | AND, x, Bil.UnOp (NOT, y) when Exp.equal x y -> (
              match width exp with
              | Some bits -> Bil.Int (Word.zero bits)
              | None -> exp)
          | AND, Bil.UnOp (NOT, y), x when Exp.equal x y -> (
              match width exp with
              | Some bits -> Bil.Int (Word.zero bits)
              | None -> exp)
          | MINUS, x, y when is_zero y -> x
          | MINUS, x, y when Exp.equal x y -> (
              match width exp with
              | Some bits -> Bil.Int (Word.zero bits)
              | None -> exp)
          | (AND | OR | XOR), x, y when Exp.equal x y -> (
              match op with
              | XOR -> (
                  match width exp with
                  | Some bits -> Bil.Int (Word.zero bits)
                  | None -> exp)
              | _ -> x)
          | TIMES, x, y when is_one x || is_one y -> if is_one x then y else x
          | TIMES, x, y when is_zero x || is_zero y -> (
              match width exp with
              | Some bits -> Bil.Int (Word.zero bits)
              | None -> exp)
          | (AND | OR | XOR), x, y when is_zero x || is_zero y -> (
              match op with
              | AND -> (
                  match width exp with
                  | Some bits -> Bil.Int (Word.zero bits)
                  | None -> exp)
              | _ -> if is_zero x then y else x)
          | AND, x, y when is_ones x || is_ones y -> if is_ones x then y else x
          | OR, x, y when is_ones x || is_ones y -> if is_ones x then x else y
          | (LSHIFT | RSHIFT | ARSHIFT), x, y when is_zero y -> x
          | _ -> exp))
  | Bil.UnOp (NOT, Bil.UnOp (NOT, x)) -> x
  | Bil.UnOp (op, Bil.Int value) -> (
      try Bil.Int (Bil.Apply.unop op value) with _ -> exp)
  | Bil.UnOp _ -> exp
  | Bil.Cast (cast, bits, Bil.Int value) -> (
      try Bil.Int (Bil.Apply.cast cast bits value) with _ -> exp)
  | Bil.Cast ((UNSIGNED | SIGNED | LOW), bits, x)
    when Option.equal Int.equal (width x) (Some bits) ->
      x
  | Bil.Cast _ -> exp
  | Bil.Extract (hi, lo, Bil.Int value) -> (
      try Bil.Int (Word.extract_exn ~hi ~lo value) with _ -> exp)
  | Bil.Extract (hi, 0, x) when Option.equal Int.equal (width x) (Some (hi + 1))
    ->
      x
  | Bil.Extract (hi, lo, Bil.Extract (_, inner_lo, x)) ->
      Bil.Extract (hi + inner_lo, lo + inner_lo, x)
  | Bil.Extract (hi, lo, Bil.Concat (x, y)) -> (
      match width y with
      | Some right when hi < right -> Bil.Extract (hi, lo, y)
      | Some right when lo >= right -> Bil.Extract (hi - right, lo - right, x)
      | _ -> exp)
  | Bil.Ite (Bil.Int condition, x, _) when not (Word.is_zero condition) -> x
  | Bil.Ite (Bil.Int condition, _, y) when Word.is_zero condition -> y
  | Bil.Ite (_, x, y) when Exp.equal x y -> x
  | _ -> exp

and simplify_children exp =
  match exp with
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> exp
  | Bil.Load (mem, addr, endian, size) ->
      Bil.Load (simplify mem, simplify addr, endian, size)
  | Bil.Store (mem, addr, value, endian, size) ->
      Bil.Store (simplify mem, simplify addr, simplify value, endian, size)
  | Bil.BinOp (op, x, y) -> Bil.BinOp (op, simplify x, simplify y)
  | Bil.UnOp (op, x) -> Bil.UnOp (op, simplify x)
  | Bil.Cast (cast, bits, x) -> Bil.Cast (cast, bits, simplify x)
  | Bil.Let (var, value, body) -> Bil.Let (var, simplify value, simplify body)
  | Bil.Ite (condition, x, y) ->
      Bil.Ite (simplify condition, simplify x, simplify y)
  | Bil.Extract (hi, lo, x) -> Bil.Extract (hi, lo, simplify x)
  | Bil.Concat (x, y) -> Bil.Concat (simplify x, simplify y)

let exp = simplify
let sub = Term.map blk_t ~f:(Blk.map_exp ~f:simplify)
