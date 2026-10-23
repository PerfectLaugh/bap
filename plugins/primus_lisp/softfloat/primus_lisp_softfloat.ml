(* The binary floating-point arithmetic of IEEE 754, exactly, in any
   format, e.g., binary16, binary32, binary64, binary80 of x87, whose
   integer bit is explicit, and binary128, with the five rounding modes,
   which the intrinsics of the lifters, e.g., fadd_rtz_ieee754_binary_32,
   run in Primus, see primus_lisp_ieee754.ml.

   The finite values are m * 2^e, whose sums and products are exact, and
   whose quotients and roots have more bits than the format, and a
   sticky bit, so that they are rounded once. The NaNs, and the integers,
   that the floats are converted to, which are out of their range, are
   of the target, see [policy]. *)

type format = { w : int; t : int; explicit : bool }
(** the bits of the exponent and of the significand, without the hidden bit,
    unless it is [explicit] *)

let format = function
  | 16 -> Some { w = 5; t = 10; explicit = false }
  | 32 -> Some { w = 8; t = 23; explicit = false }
  | 64 -> Some { w = 11; t = 52; explicit = false }
  | 80 -> Some { w = 15; t = 64; explicit = true }
  | 128 -> Some { w = 15; t = 112; explicit = false }
  | _ -> None

let size f = 1 + f.w + f.t

(* the bits of the significand, with the integer bit *)
let precision f = if f.explicit then f.t else f.t + 1
let bias f = (1 lsl (f.w - 1)) - 1

type rmode = Rne | Rtz | Rtp | Rtn | Rna

type policy = {
  default_negative : bool;  (** the default NaN is negative, as on x86 *)
  canonical : bool;  (** the NaNs are not propagated, as on RISC-V *)
  first : bool;
      (** the first NaN operand is the result, as on x86, else the first
          signaling one, then the first quiet one, as on ARM *)
  invalid_int : [ `Indefinite | `Saturate_zero | `Saturate_max | `Saturate_min ];
      (** the integer of a NaN, or of a float out of the range: the minimal
          signed integer, or the maximal unsigned one, as on x86, or the bound,
          and 0, the maximum, or the minimum for the NaN *)
}

let default_policy =
  {
    default_negative = false;
    canonical = false;
    first = false;
    invalid_int = `Saturate_zero;
  }

type value =
  | Nan of { sign : bool; quiet : bool; payload : Z.t }
      (** the payload is the fraction without its quiet bit *)
  | Inf of bool
  | Fin of { sign : bool; m : Z.t; e : int }  (** (-1)^sign * m * 2^e *)

let bit x i = Z.testbit x i
let ones n = Z.(pred (shift_left one n))
let field x lo n = Z.(logand (shift_right x lo) (ones n))

let decode f x =
  let sign = bit x (f.w + f.t) in
  let exp = Z.to_int (field x f.t f.w) in
  let frac = field x 0 f.t in
  let emax = (1 lsl f.w) - 1 in
  (* the fraction, without the integer bit of x87 *)
  let fbits = if f.explicit then f.t - 1 else f.t in
  let fraction = field frac 0 fbits in
  let nan () =
    Nan
      {
        sign;
        quiet = bit fraction (fbits - 1);
        payload = field fraction 0 (fbits - 1);
      }
  in
  if exp = emax then if Z.equal fraction Z.zero then Inf sign else nan ()
  else if f.explicit && exp <> 0 && not (bit frac (f.t - 1)) then
    (* the unnormals of x87 are invalid *)
    nan ()
  else
    let e0 = 1 - bias f - (precision f - 1) in
    if exp = 0 then Fin { sign; m = frac; e = e0 }
    else
      let m = if f.explicit then frac else Z.(frac + shift_left one f.t) in
      Fin { sign; m; e = exp - bias f - (precision f - 1) }

let encode_nan f ~sign ~payload =
  let negative = sign in
  let fbits = if f.explicit then f.t - 1 else f.t in
  let q = fbits - 1 in
  let fraction = Z.(logor (shift_left one q) (logand payload (ones q))) in
  let j = f.t - 1 and top = f.w + f.t in
  let frac =
    if f.explicit then Z.(logor (shift_left one j) fraction) else fraction
  in
  let exp = Z.of_int ((1 lsl f.w) - 1) in
  Z.(
    logor
      (shift_left (if negative then one else zero) top)
      (logor (shift_left exp f.t) frac))

let default_nan policy f =
  encode_nan f ~sign:policy.default_negative ~payload:Z.zero

let encode_parts f ~sign ~exp ~frac =
  let top = f.w + f.t and negative = sign in
  Z.(
    logor
      (shift_left (if negative then one else zero) top)
      (logor (shift_left (of_int exp) f.t) frac))

let encode_inf f sign =
  let frac = if f.explicit then Z.shift_left Z.one (f.t - 1) else Z.zero in
  encode_parts f ~sign ~exp:((1 lsl f.w) - 1) ~frac

let encode_zero f sign = encode_parts f ~sign ~exp:0 ~frac:Z.zero

(* the largest finite value *)
let encode_max f sign =
  let frac = if f.explicit then ones f.t else ones f.t in
  encode_parts f ~sign ~exp:((1 lsl f.w) - 2) ~frac

(* [shift_round rm ~sign ~sticky m s] is [m / 2^s], rounded, with the bits
   below [m] in [sticky] *)
let shift_round rm ~sign ~sticky m s =
  if s <= 0 then (Z.shift_left m (-s), sticky)
  else
    let kept = Z.shift_right m s in
    let rem = Z.logand m (ones s) in
    let half = Z.shift_left Z.one (s - 1) in
    let inexact = sticky || not (Z.equal rem Z.zero) in
    let up =
      match rm with
      | Rtz -> false
      | Rtp -> inexact && not sign
      | Rtn -> inexact && sign
      | Rna -> Z.geq rem half
      | Rne ->
          let c = Z.compare rem half in
          c > 0 || (c = 0 && (sticky || bit kept 0))
    in
    ((if up then Z.succ kept else kept), inexact)

(* the finite value, with the bits below it in [sticky], rounded to the
   format, e.g., to a subnormal, to the infinity, or to zero *)
let round f rm ~sign ?(sticky = false) m e =
  if Z.equal m Z.zero && not sticky then encode_zero f sign
  else
    let p = precision f in
    let emin = 1 - bias f in
    let n = Z.numbits m in
    let lead = e + n - 1 in
    let lsb = max (lead - (p - 1)) (emin - (p - 1)) in
    let kept, _ = shift_round rm ~sign ~sticky m (lsb - e) in
    let kept, lsb =
      if Z.numbits kept > p then (Z.shift_right kept 1, lsb + 1) else (kept, lsb)
    in
    if Z.equal kept Z.zero then encode_zero f sign
    else
      let lead = lsb + Z.numbits kept - 1 in
      if lead > bias f then
        match rm with
        | Rne | Rna -> encode_inf f sign
        | Rtz -> encode_max f sign
        | Rtp -> if sign then encode_max f sign else encode_inf f sign
        | Rtn -> if sign then encode_inf f sign else encode_max f sign
      else if Z.numbits kept = p then
        let frac =
          if f.explicit then kept else Z.sub kept (Z.shift_left Z.one (p - 1))
        in
        encode_parts f ~sign ~exp:(lead + bias f) ~frac
      else encode_parts f ~sign ~exp:0 ~frac:kept

(* the NaN of the result: the first NaN operand, quiet, or the default
   one *)
let propagate policy f operands =
  if policy.canonical then default_nan policy f
  else
    let first q =
      List.find_map
        (function
          | Nan { sign; quiet; payload } when q quiet ->
              Some (encode_nan f ~sign ~payload)
          | _ -> None)
        operands
    in
    match first (fun q -> (not q) || policy.first) with
    | Some x -> x
    | None -> (
        match first (fun q -> q) with
        | Some x -> x
        | None -> default_nan policy f)

let has_nan = List.exists (function Nan _ -> true | _ -> false)

let add policy f rm x y ~sub =
  let x = decode f x and y = decode f y in
  let y =
    if not sub then y
    else
      match y with
      | Fin r -> Fin { r with sign = not r.sign }
      | Inf s -> Inf (not s)
      | n -> n
  in
  if has_nan [ x; y ] then propagate policy f [ x; y ]
  else
    match (x, y) with
    | Inf a, Inf b when a <> b -> default_nan policy f
    | Inf s, _ | _, Inf s -> encode_inf f s
    | Fin { sign = sa; m = ma; e = ea }, Fin { sign = sb; m = mb; e = eb } ->
        let e = min ea eb in
        let v sign m e' =
          let v = Z.shift_left m (e' - e) in
          if sign then Z.neg v else v
        in
        let m = Z.add (v sa ma ea) (v sb mb eb) in
        if Z.equal m Z.zero then
          (* the exact zero is negative, if both are, or as rtn rounds *)
          encode_zero f ((sa && sb) || (sa <> sb && rm = Rtn))
        else round f rm ~sign:(Z.sign m < 0) (Z.abs m) e
    | _ -> default_nan policy f

let mul policy f rm x y =
  let x = decode f x and y = decode f y in
  if has_nan [ x; y ] then propagate policy f [ x; y ]
  else
    match (x, y) with
    | Inf a, Inf b -> encode_inf f (a <> b)
    | Inf s, Fin r | Fin r, Inf s ->
        if Z.equal r.m Z.zero then default_nan policy f
        else encode_inf f (s <> r.sign)
    | Fin a, Fin b ->
        round f rm ~sign:(a.sign <> b.sign) Z.(a.m * b.m) (a.e + b.e)
    | _ -> default_nan policy f

(* x * y + z, rounded once *)
let fma policy f rm x y z =
  let x = decode f x and y = decode f y and z = decode f z in
  if has_nan [ x; y; z ] then propagate policy f [ x; y; z ]
  else
    let is_zero = function Fin { m; _ } -> Z.equal m Z.zero | _ -> false in
    let product =
      match (x, y) with
      | Inf a, Inf b -> `Inf (a <> b)
      | Inf s, (Fin { sign; _ } as r) | (Fin { sign; _ } as r), Inf s ->
          if is_zero r then `Invalid else `Inf (s <> sign)
      | Fin a, Fin b -> `Fin (a.sign <> b.sign, Z.mul a.m b.m, a.e + b.e)
      | _ -> `Invalid
    in
    match (product, z) with
    | `Invalid, _ -> default_nan policy f
    | `Inf a, Inf b when a <> b -> default_nan policy f
    | `Inf s, _ -> encode_inf f s
    | `Fin _, Inf s -> encode_inf f s
    | `Fin (sp, mp, ep), Fin { sign = sz; m = mz; e = ez } ->
        let e = min ep ez in
        let v sign m e' =
          let v = Z.shift_left m (e' - e) in
          if sign then Z.neg v else v
        in
        let m = Z.add (v sp mp ep) (v sz mz ez) in
        if Z.equal m Z.zero then
          encode_zero f ((sp && sz) || (sp <> sz && rm = Rtn))
        else round f rm ~sign:(Z.sign m < 0) (Z.abs m) e
    | _ -> default_nan policy f

let div policy f rm x y =
  let x = decode f x and y = decode f y in
  if has_nan [ x; y ] then propagate policy f [ x; y ]
  else
    match (x, y) with
    | Inf _, Inf _ -> default_nan policy f
    | Inf a, Fin b -> encode_inf f (a <> b.sign)
    | Fin a, Inf b -> encode_zero f (a.sign <> b)
    | Fin a, Fin b ->
        let sign = a.sign <> b.sign in
        if Z.equal b.m Z.zero then
          if Z.equal a.m Z.zero then default_nan policy f else encode_inf f sign
        else if Z.equal a.m Z.zero then encode_zero f sign
        else
          (* the quotient has, at least, the bits of the format and two *)
          let s = precision f + 3 + Z.numbits b.m in
          let q, r = Z.div_rem (Z.shift_left a.m s) b.m in
          round f rm ~sign ~sticky:(not (Z.equal r Z.zero)) q (a.e - b.e - s)
    | _ -> default_nan policy f

let sqrt policy f rm x =
  match decode f x with
  | Nan _ as n -> propagate policy f [ n ]
  | Inf false -> encode_inf f false
  | Inf true -> default_nan policy f
  | Fin { sign; m; _ } when Z.equal m Z.zero -> encode_zero f sign
  | Fin { sign = true; _ } -> default_nan policy f
  | Fin { m; e; _ } ->
      (* the root of an even exponent, with the bits of the format and
         two *)
      let s = (2 * (precision f + 3)) + Z.numbits m in
      let s = if (e - s) land 1 = 0 then s else s + 1 in
      let r, rem = Z.sqrt_rem (Z.shift_left m s) in
      round f rm ~sign:false ~sticky:(not (Z.equal rem Z.zero)) r ((e - s) / 2)

(* the value, rounded to an integer, in the same format *)
let round_integral policy f rm x =
  match decode f x with
  | Nan _ as n -> propagate policy f [ n ]
  | Inf _ -> x
  | Fin { e; _ } when e >= 0 -> x
  | Fin { sign; m; e } ->
      let kept, _ = shift_round rm ~sign ~sticky:false m (-e) in
      if Z.equal kept Z.zero then encode_zero f sign
      else round f rm ~sign kept 0

let convert policy fi fo rm x =
  match decode fi x with
  | Nan { sign; payload; _ } ->
      if policy.canonical then default_nan policy fo
      else
        (* the payload keeps its upper bits *)
        let bi = (if fi.explicit then fi.t - 1 else fi.t) - 1
        and bo = (if fo.explicit then fo.t - 1 else fo.t) - 1 in
        let payload =
          if bo >= bi then Z.shift_left payload (bo - bi)
          else Z.shift_right payload (bi - bo)
        in
        encode_nan fo ~sign ~payload
  | Inf s -> encode_inf fo s
  | Fin { sign; m; e } -> round fo rm ~sign m e

(* the integer of [width] bits as the float *)
let of_int f rm ~signed ~width x =
  let x = Z.logand x (ones width) in
  let x =
    if signed && bit x (width - 1) then Z.(x - shift_left one width) else x
  in
  round f rm ~sign:(Z.sign x < 0) (Z.abs x) 0

(* the float as the integer of [width] bits, rounded, or the invalid
   integer of the policy, if it is out of the range *)
let to_int policy f rm ~signed ~width x =
  let lo = if signed then Z.neg (Z.shift_left Z.one (width - 1)) else Z.zero in
  let hi = if signed then ones (width - 1) else ones width in
  let wrap v = Z.logand v (ones width) in
  let invalid ~nan ~sign =
    wrap
      (match policy.invalid_int with
      | `Indefinite -> if signed then lo else ones width
      | `Saturate_zero -> if nan then Z.zero else if sign then lo else hi
      | `Saturate_max -> if nan then hi else if sign then lo else hi
      | `Saturate_min -> if nan then lo else if sign then lo else hi)
  in
  match decode f x with
  | Nan _ -> invalid ~nan:true ~sign:false
  | Inf sign -> invalid ~nan:false ~sign
  | Fin { sign; m; e } ->
      let v =
        if e >= 0 then Z.shift_left m e
        else fst (shift_round rm ~sign ~sticky:false m (-e))
      in
      let v = if sign then Z.neg v else v in
      if Z.lt v lo || Z.gt v hi then invalid ~nan:false ~sign else wrap v

(* the order of the values, which aren't NaNs: the negative infinity,
   the negative values, the zeros, the positive values, and the positive
   infinity *)
let compare_values a b =
  let cls = function
    | Inf true -> 0
    | Fin { m; _ } when Z.equal m Z.zero -> 2
    | Fin { sign = true; _ } -> 1
    | Fin _ -> 3
    | Inf false | Nan _ -> 4
  in
  match (a, b) with
  | Fin { m = mx; e = ex; _ }, Fin { m = my; e = ey; _ }
    when cls a = cls b && (cls a = 1 || cls a = 3) ->
      let e = min ex ey in
      let c = Z.compare (Z.shift_left mx (ex - e)) (Z.shift_left my (ey - e)) in
      if cls a = 1 then -c else c
  | _ -> compare (cls a) (cls b)

(* if x < y, which the NaNs are not ordered by *)
let less f x y =
  match (decode f x, decode f y) with
  | Nan _, _ | _, Nan _ -> false
  | a, b -> compare_values a b < 0

let is_nan f x = match decode f x with Nan _ -> true | _ -> false
let is_inf f x = match decode f x with Inf _ -> true | _ -> false

let%test_module _ =
  (module struct
    let f64 = Option.get (format 64)
    let f32 = Option.get (format 32)
    let z64 x = Z.of_int64_unsigned (Int64.bits_of_float x)
    let z32 x = Z.of_int32_unsigned (Int32.bits_of_float x)
    let of32 x = Int32.float_of_bits (Z.to_int32_unsigned x)
    let of64 x = Int64.float_of_bits (Z.to_int64_unsigned x)
    let p = default_policy

    let samples =
      [
        0.;
        -0.;
        1.;
        -1.;
        0.1;
        3.5;
        1e300;
        -1e-300;
        4.9e-324;
        1.5e-320;
        123456789.123;
        infinity;
        neg_infinity;
        2.2250738585072014e-308;
        1.7976931348623157e308;
        0.3333333333333333;
        -7.25;
      ]

    let same a b =
      Int64.(equal (bits_of_float a) (bits_of_float b))
      || (Float.is_nan a && Float.is_nan b)

    let%test "binary64 as the host" =
      List.for_all
        (fun a ->
          List.for_all
            (fun b ->
              same (of64 (add p f64 Rne (z64 a) (z64 b) ~sub:false)) (a +. b)
              && same (of64 (add p f64 Rne (z64 a) (z64 b) ~sub:true)) (a -. b)
              && same (of64 (mul p f64 Rne (z64 a) (z64 b))) (a *. b)
              && same (of64 (div p f64 Rne (z64 a) (z64 b))) (a /. b))
            samples
          && same (of64 (sqrt p f64 Rne (z64 a))) (Float.sqrt a))
        samples

    let%test "binary32 as the host" =
      let r x = Int32.float_of_bits (Int32.bits_of_float x) in
      let samples = List.map r samples in
      List.for_all
        (fun a ->
          List.for_all
            (fun b ->
              same
                (of32 (add p f32 Rne (z32 a) (z32 b) ~sub:false))
                (r (a +. b))
              && same (of32 (mul p f32 Rne (z32 a) (z32 b))) (r (a *. b))
              && same (of32 (div p f32 Rne (z32 a) (z32 b))) (r (a /. b)))
            samples
          && same (of32 (sqrt p f32 Rne (z32 a))) (r (Float.sqrt a)))
        samples

    let%test "fused" =
      (* 0.1 * 10 - 1 is the error of the rounding of 0.1 *)
      of64 (fma p f64 Rne (z64 0.1) (z64 10.) (z64 (-1.)))
      = Float.fma 0.1 10. (-1.)
      && of64 (fma p f64 Rne (z64 0.1) (z64 10.) (z64 (-1.))) <> 0.

    let%test "directed rounding" =
      let third m = of64 (div p f64 m (z64 1.) (z64 3.)) in
      third Rtz < third Rtp && third Rtn = third Rtz && third Rne = 1. /. 3.

    let%test "conversions" =
      of32 (convert p f64 f32 Rne (z64 0.1))
      = Int32.float_of_bits (Int32.bits_of_float 0.1)
      && Z.equal
           (to_int p f64 Rtz ~signed:true ~width:32 (z64 (-2.7)))
           (Z.of_int 0xFFFFFFFE)
      && Z.equal
           (to_int p f64 Rne ~signed:true ~width:32 (z64 2.5))
           (Z.of_int 2)
      && of64 (of_int f64 Rne ~signed:true ~width:32 (Z.of_int 0xFFFFFFFF))
         = -1.
      && of64 (round_integral p f64 Rtn (z64 (-0.5))) = -1.

    let%test "x87" =
      let f80 = Option.get (format 80) in
      let one = convert p f64 f80 Rne (z64 1.) in
      Z.equal one Z.(logor (shift_left (of_int 16383) 64) (shift_left one 63))
      && of64 (convert p f80 f64 Rne (add p f80 Rne one one ~sub:false)) = 2.
  end)

(* the policy of [ieee754-op], see ieee754-intrinsics.lisp: the bit 0, the
   negative default NaN, the bit 1, the canonical NaNs, the bit 2, the
   first NaN operand, and the bits 4 and 5, the invalid integers *)
let policy_of_int policy =
  {
    default_negative = policy land 1 <> 0;
    canonical = policy land 2 <> 0;
    first = policy land 4 <> 0;
    invalid_int =
      (match (policy lsr 4) land 3 with
      | 1 -> `Indefinite
      | 2 -> `Saturate_max
      | 3 -> `Saturate_min
      | _ -> `Saturate_zero);
  }

let rmode_of_int = function
  | 1 -> Rtz
  | 2 -> Rtp
  | 3 -> Rtn
  | 4 -> Rna
  | _ -> Rne

(* the operation [op] of [ieee754-op], whose operands are of [src] bits,
   and the result of [dst] bits, a boolean of 1 bit, or [None] *)
let apply ~op ~rm ~src ~dst policy args =
  match (format src, format dst) with
  | exception _ -> None
  | fsrc, fdst -> (
      let fmt = function Some f -> f | None -> raise Not_found in
      let mask width x = Z.logand x (Z.pred (Z.shift_left Z.one width)) in
      let word x = Some (mask dst x) in
      let bool b = Some (if b then Z.one else Z.zero) in
      try
        match (op, args) with
        | 1, [ x; y ] -> word (add policy (fmt fsrc) rm x y ~sub:false)
        | 2, [ x; y ] -> word (add policy (fmt fsrc) rm x y ~sub:true)
        | 3, [ x; y ] -> word (mul policy (fmt fsrc) rm x y)
        | 4, [ x; y ] -> word (div policy (fmt fsrc) rm x y)
        | 5, [ x ] -> word (sqrt policy (fmt fsrc) rm x)
        | 6, [ x ] -> word (round_integral policy (fmt fsrc) rm x)
        | 7, [ x ] -> word (convert policy (fmt fsrc) (fmt fdst) rm x)
        | 8, [ x ] -> word (of_int (fmt fdst) rm ~signed:false ~width:src x)
        | 9, [ x ] -> word (of_int (fmt fdst) rm ~signed:true ~width:src x)
        | 10, [ x ] ->
            word (to_int policy (fmt fsrc) rm ~signed:false ~width:dst x)
        | 11, [ x ] ->
            word (to_int policy (fmt fsrc) rm ~signed:true ~width:dst x)
        | 12, [ x; y ] -> bool (less (fmt fsrc) x y)
        | 13, [ x ] -> bool (is_nan (fmt fsrc) x)
        | 14, [ x ] -> bool (is_inf (fmt fsrc) x)
        | 15, [ x; y; z ] -> word (fma policy (fmt fsrc) rm x y z)
        | _ -> None
      with Not_found -> None)

(* the operations of the intrinsics, see ieee754-intrinsics.py *)
let ops =
  [
    ("fadd", 1);
    ("fsub", 2);
    ("fmul", 3);
    ("fdiv", 4);
    ("fsqrt", 5);
    ("fround", 6);
    ("fconvert", 7);
    ("cast_float", 8);
    ("cast_sfloat", 9);
    ("cast_int", 10);
    ("cast_sint", 11);
    ("forder", 12);
    ("is_nan", 13);
    ("is_inf", 14);
    ("fmad", 15);
  ]

let rmodes = [ ("rne", 0); ("rtz", 1); ("rtp", 2); ("rtn", 3); ("rna", 4) ]

(* the intrinsic, e.g., fadd_rtz_ieee754_binary_32, or
   cast_int_rne_ieee754_binary_64_32, as its operation, its rounding
   mode, and the sizes of its operands and of its result *)
let intrinsic name =
  match Core.String.substr_index name ~pattern:"ieee754_binary_" with
  | None -> None
  | Some i -> (
      let prefix = Core.String.prefix name i in
      let sizes =
        Core.String.drop_prefix name (i + Core.String.length "ieee754_binary_")
        |> Core.String.split ~on:'_'
        |> Core.List.map ~f:Core.Int.of_string_opt
      in
      let prefix = Core.String.chop_suffix_if_exists prefix ~suffix:"_" in
      let op, rm =
        match Core.String.rsplit2 prefix ~on:'_' with
        | Some (op, rm)
          when Core.List.Assoc.mem rmodes rm ~equal:Core.String.equal ->
            (op, Core.List.Assoc.find_exn rmodes rm ~equal:Core.String.equal)
        | _ -> (prefix, 0)
      in
      match (Core.List.Assoc.find ops op ~equal:Core.String.equal, sizes) with
      | Some op, [ Some src ] ->
          let dst = if op >= 12 && op <= 14 then 1 else src in
          Some (op, rm, src, dst)
      | Some op, [ Some src; Some dst ] -> Some (op, rm, src, dst)
      | _ -> None)
