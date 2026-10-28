open Core
open Bap.Std

type t = {
  bits : int;
  known : Word.t;
  value : Word.t;
  lo : Word.t;
  hi : Word.t;
}

let top bits =
  {
    bits;
    known = Word.zero bits;
    value = Word.zero bits;
    lo = Word.zero bits;
    hi = Word.ones bits;
  }

let constant word =
  let bits = Word.bitwidth word in
  { bits; known = Word.ones bits; value = word; lo = word; hi = word }

let is_exact range = Word.equal range.known (Word.ones range.bits)
let exact range = if is_exact range then Some range.value else None

let known_bit range bit =
  if Word.is_zero (Word.extract_exn ~hi:bit ~lo:bit range.known) then None
  else Some (not (Word.is_zero (Word.extract_exn ~hi:bit ~lo:bit range.value)))

let nonnegative range =
  Option.equal Bool.equal (known_bit range (range.bits - 1)) (Some false)

let negative range =
  Option.equal Bool.equal (known_bit range (range.bits - 1)) (Some true)

let cast_unsigned bits range =
  if range.bits = bits then range
  else if range.bits < bits then
    {
      bits;
      known = Word.concat (Word.ones (bits - range.bits)) range.known;
      value = Word.concat (Word.zero (bits - range.bits)) range.value;
      lo = Word.concat (Word.zero (bits - range.bits)) range.lo;
      hi = Word.concat (Word.zero (bits - range.bits)) range.hi;
    }
  else
    let known = Word.extract_exn ~hi:(bits - 1) ~lo:0 range.known in
    let value = Word.extract_exn ~hi:(bits - 1) ~lo:0 range.value in
    let lo = Word.extract_exn ~hi:(bits - 1) ~lo:0 range.lo in
    let hi = Word.extract_exn ~hi:(bits - 1) ~lo:0 range.hi in
    { bits; known; value; lo; hi }

let apply_unop op range =
  match exact range with
  | Some value -> (
      try constant (Bil.Apply.unop op value) with _ -> top range.bits)
  | None -> (
      match op with
      | Bil.NOT ->
          { (top range.bits) with value = Word.logxor range.value range.known }
      | Bil.NEG -> top range.bits)

let bitwise op left right =
  let bits = left.bits in
  if left.bits <> right.bits then top bits
  else
    match (exact left, exact right) with
    | Some x, Some y -> (
        try constant (Bil.Apply.binop op x y) with _ -> top bits)
    | _ -> (
        match op with
        | Bil.AND ->
            let known = Word.logor left.known right.known in
            let value = Word.logand left.value right.value in
            { (top bits) with known; value }
        | Bil.OR ->
            let known = Word.logand left.known right.known in
            let value = Word.logor left.value right.value in
            { (top bits) with known; value }
        | Bil.XOR ->
            let known = Word.logand left.known right.known in
            let value = Word.logxor left.value right.value in
            { (top bits) with known; value }
        | _ -> top bits)

let rec eval env exp =
  let eval_x = eval env in
  match exp with
  | Bil.Int value -> constant value
  | Bil.Var var ->
      Map.find env var |> Option.value ~default:(top (bitwidth exp))
  | Bil.Unknown (_, Type.Imm bits) -> top bits
  | Bil.Unknown _ -> top 0
  | Bil.Cast (UNSIGNED, bits, value) -> cast_unsigned bits (eval_x value)
  | Bil.Cast ((SIGNED | LOW | HIGH), bits, value) -> (
      match exact (eval_x value) with
      | Some value -> (
          try
            constant
              (Bil.Apply.cast
                 (match exp with
                 | Bil.Cast (kind, _, _) -> kind
                 | _ -> assert false)
                 bits value)
          with _ -> top bits)
      | None -> top bits)
  | Bil.Extract (hi, lo, value) -> (
      let range = eval_x value in
      match exact range with
      | Some value -> constant (Word.extract_exn ~hi ~lo value)
      | None ->
          let known = Word.extract_exn ~hi ~lo range.known in
          let value = Word.extract_exn ~hi ~lo range.value in
          {
            bits = hi - lo + 1;
            known;
            value;
            lo = Word.zero (hi - lo + 1);
            hi = Word.ones (hi - lo + 1);
          })
  | Bil.UnOp (op, value) -> apply_unop op (eval_x value)
  | Bil.BinOp (((AND | OR | XOR) as op), left, right) ->
      bitwise op (eval_x left) (eval_x right)
  | Bil.BinOp (op, left, right) -> (
      match (exact (eval_x left), exact (eval_x right)) with
      | Some left, Some right -> (
          try constant (Bil.Apply.binop op left right)
          with _ -> top (bitwidth exp))
      | _ -> top (bitwidth exp))
  | Bil.Concat (left, right) -> (
      match (exact (eval_x left), exact (eval_x right)) with
      | Some left, Some right -> constant (Word.concat left right)
      | _ -> top (bitwidth exp))
  | Bil.Ite (condition, yes, no) -> (
      match exact (eval_x condition) with
      | Some condition when not (Word.is_zero condition) -> eval_x yes
      | Some _ -> eval_x no
      | None -> join (eval_x yes) (eval_x no))
  | Bil.Let (var, value, body) ->
      let value = eval_x value in
      eval (Map.set env ~key:var ~data:value) body
  | Bil.Load _ | Bil.Store _ -> top (bitwidth exp)

and join left right =
  if left.bits <> right.bits then top left.bits
  else
    let known = Word.logand left.known right.known in
    let value =
      Word.logand
        (Word.logor left.value right.value)
        (Word.logand left.known right.known)
    in
    let lo =
      if Word.Unsigned_value_order.compare left.lo right.lo <= 0 then left.lo
      else right.lo
    in
    let hi =
      if Word.Unsigned_value_order.compare left.hi right.hi >= 0 then left.hi
      else right.hi
    in
    { bits = left.bits; known; value; lo; hi }

and bitwidth exp =
  match Type.infer exp with Ok (Type.Imm bits) -> bits | _ -> 0

let operation = function
  | Bil.BinOp (op, _, _) -> (
      match op with
      | SLT -> "slt"
      | SLE -> "sle"
      | EQ -> "eq"
      | NEQ -> "neq"
      | _ -> "other")
  | _ -> "other"

let rewrite_with_env env exp =
  let rec map f exp =
    let exp =
      match exp with
      | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> exp
      | Bil.Load (mem, addr, endian, size) ->
          Bil.Load (map f mem, map f addr, endian, size)
      | Bil.Store (mem, addr, value, endian, size) ->
          Bil.Store (map f mem, map f addr, map f value, endian, size)
      | Bil.BinOp (op, left, right) -> Bil.BinOp (op, map f left, map f right)
      | Bil.UnOp (op, value) -> Bil.UnOp (op, map f value)
      | Bil.Cast (kind, bits, value) -> Bil.Cast (kind, bits, map f value)
      | Bil.Let (var, value, body) -> Bil.Let (var, map f value, map f body)
      | Bil.Ite (condition, yes, no) ->
          Bil.Ite (map f condition, map f yes, map f no)
      | Bil.Extract (hi, lo, value) -> Bil.Extract (hi, lo, map f value)
      | Bil.Concat (left, right) -> Bil.Concat (map f left, map f right)
    in
    f exp
  in
  let comparison =
    Decompile_rule.rule ~operations:[ "slt"; "sle" ] "signed-to-unsigned"
      (function
      | Bil.BinOp (((SLT | SLE) as op), left, right)
        when nonnegative (eval env left) && nonnegative (eval env right) ->
          Some
            (Bil.BinOp
               ( (match op with SLT -> LT | SLE -> LE | _ -> assert false),
                 left,
                 right ))
      | _ -> None)
  in
  let equality =
    Decompile_rule.rule ~operations:[ "eq"; "neq" ] "constant-equality"
      (function
      | Bil.BinOp (((EQ | NEQ) as op), left, right) as exp -> (
          match (exact (eval env left), exact (eval env right)) with
          | Some left, Some right ->
              let equal = Word.equal left right in
              let truth =
                match op with
                | EQ -> equal
                | NEQ -> not equal
                | _ -> assert false
              in
              Some (Bil.Int (Word.of_bool truth))
          | _ -> Some exp)
      | _ -> None)
  in
  Decompile_rule.run ~key:operation ~equal:Exp.equal ~map
    [ comparison; equality ] exp
  |> fst

let simplify_sub sub =
  Term.map blk_t sub ~f:(fun blk ->
      let env = ref Var.Map.empty in
      let blk =
        Term.map def_t blk ~f:(fun def ->
            let rhs = rewrite_with_env !env (Def.rhs def) in
            env := Map.set !env ~key:(Def.lhs def) ~data:(eval !env rhs);
            Def.with_rhs def rhs)
      in
      Term.map jmp_t blk ~f:(fun jmp ->
          Jmp.with_cond jmp (rewrite_with_env !env (Jmp.cond jmp))))

let sign_nonnegative range = nonnegative range
let sign_negative range = negative range
let value range = exact range
let join_ranges = join
