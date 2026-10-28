type t
type bytes = (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t
type modulus = int
type 'a m = modulus -> 'a

module Native = struct
  external zero : unit -> t = "bitvec_rs_zero"
  external one : unit -> t = "bitvec_rs_one"
  external bool : bool -> t = "bitvec_rs_bool"
  external int : int -> int -> t = "bitvec_rs_int"
  external int32 : int32 -> int -> t = "bitvec_rs_int32"
  external int64 : int64 -> int -> t = "bitvec_rs_int64"
  external bigint : string -> int -> (t, string) result = "bitvec_rs_bigint"
  external to_bigint : t -> string = "bitvec_rs_to_bigint"
  external ones : int -> t = "bitvec_rs_ones"
  external succ : t -> int -> t = "bitvec_rs_succ"
  external pred : t -> int -> t = "bitvec_rs_pred"
  external nsucc : t -> int -> int -> t = "bitvec_rs_nsucc"
  external npred : t -> int -> int -> t = "bitvec_rs_npred"
  external neg : t -> int -> t = "bitvec_rs_neg"
  external lnot : t -> int -> t = "bitvec_rs_lnot"
  external abs : t -> int -> t = "bitvec_rs_abs"
  external add : t -> t -> int -> t = "bitvec_rs_add"
  external sub : t -> t -> int -> t = "bitvec_rs_sub"
  external mul : t -> t -> int -> t = "bitvec_rs_mul"
  external div : t -> t -> int -> t = "bitvec_rs_div"
  external sdiv : t -> t -> int -> t = "bitvec_rs_sdiv"
  external rem : t -> t -> int -> t = "bitvec_rs_rem"
  external srem : t -> t -> int -> t = "bitvec_rs_srem"
  external smod : t -> t -> int -> t = "bitvec_rs_smod"
  external logand : t -> t -> int -> t = "bitvec_rs_logand"
  external logor : t -> t -> int -> t = "bitvec_rs_logor"
  external logxor : t -> t -> int -> t = "bitvec_rs_logxor"
  external lshift : t -> t -> int -> t = "bitvec_rs_lshift"
  external rshift : t -> t -> int -> t = "bitvec_rs_rshift"
  external arshift : t -> t -> int -> t = "bitvec_rs_arshift"
  external gcd : t -> t -> int -> t = "bitvec_rs_gcd"
  external lcm : t -> t -> int -> t = "bitvec_rs_lcm"
  external gcdext : t -> t -> int -> t * t * t = "bitvec_rs_gcdext"
  external nth : t -> int -> (bool, string) result = "bitvec_rs_nth"
  external msb : t -> int -> bool = "bitvec_rs_msb"
  external lsb : t -> bool = "bitvec_rs_lsb"
  external compare : t -> t -> int = "bitvec_rs_compare"
  external hash : t -> int = "bitvec_rs_hash"
  external to_string : t -> string = "bitvec_rs_to_string"
  external of_string : string -> (t, string) result = "bitvec_rs_of_string"
  external of_string_base : int -> string -> (t, string) result = "bitvec_rs_of_string_base"
  external to_binary : t -> bytes = "bitvec_rs_to_binary"
  external of_binary : bytes -> (t, string) result = "bitvec_rs_of_binary"
  external extract : t -> int -> int -> (t, string) result = "bitvec_rs_extract"
  external append : int -> int -> t -> t -> t = "bitvec_rs_append"
  external fits_int : t -> int -> bool = "bitvec_rs_fits_int"
  external fits_int32 : t -> bool = "bitvec_rs_fits_int32"
  external fits_int64 : t -> bool = "bitvec_rs_fits_int64"
  external to_int : t -> int -> (int, string) result = "bitvec_rs_to_int"
  external to_int32 : t -> (int32, string) result = "bitvec_rs_to_int32"
  external to_int64 : t -> (int64, string) result = "bitvec_rs_to_int64"
end

external ( mod ) : 'a m -> modulus -> 'a = "%apply"

let invalid = function Ok x -> x | Error message -> invalid_arg message
let fail = function Ok x -> x | Error message -> failwith message
let modulus w = w
let m1 = modulus 1
let m8 = modulus 8
let m16 = modulus 16
let m32 = modulus 32
let m64 = modulus 64
let zero = Native.zero ()
let one = Native.one ()
let ones = Native.ones
let bool = Native.bool
let int = Native.int
let int32 = Native.int32
let int64 = Native.int64
let bigint x m = Native.bigint (Z.to_string x) m |> invalid
let bigint_unsafe x = Native.of_string (Z.to_string x) |> invalid
let to_bigint x = Z.of_string (Native.to_bigint x)
let succ = Native.succ
let pred = Native.pred
let nsucc = Native.nsucc
let npred = Native.npred
let neg = Native.neg
let lnot = Native.lnot
let abs = Native.abs
let add = Native.add
let sub = Native.sub
let mul = Native.mul
let div = Native.div
let sdiv = Native.sdiv
let rem = Native.rem
let srem = Native.srem
let smod = Native.smod
let logand = Native.logand
let logor = Native.logor
let logxor = Native.logxor
let lshift = Native.lshift
let rshift = Native.rshift
let arshift = Native.arshift
let gcd = Native.gcd
let lcm = Native.lcm
let gcdext = Native.gcdext
let nth x n _ = Native.nth x n |> invalid
let msb = Native.msb
let lsb x _ = Native.lsb x
let compare = Native.compare
let hash = Native.hash
let extract ~hi ~lo x = Native.extract x hi lo |> invalid
let append = Native.append

let select bits x =
  let rec loop n y = function
    | [] -> y
    | bit :: rest ->
        let y = append 1 n (bool (nth x bit m1)) y in
        loop (n + 1) y rest
  in
  loop 0 zero bits

let repeat m ~times:n x =
  let rec loop i width y =
    if i < n then loop (i + 1) (width + m) (append width m y x) else y
  in
  loop 0 0 zero

let concat m xs = List.fold_left (fun y x -> append m m y x) zero xs

module Syntax = struct
  let ( !! ) x m = int x m
  let ( ~- ) x m = neg x m
  let ( ~~ ) x m = lnot x m
  let ( + ) x y m = add x y m
  let ( - ) x y m = sub x y m
  let ( * ) x y m = mul x y m
  let ( / ) x y m = div x y m
  let ( /$ ) x y m = sdiv x y m
  let ( % ) x y m = rem x y m
  let ( %$ ) x y m = smod x y m
  let ( %^ ) x y m = srem x y m
  let ( land ) x y m = logand x y m
  let ( lor ) x y m = logor x y m
  let ( lxor ) x y m = logxor x y m
  let ( lsl ) x y m = lshift x y m
  let ( lsr ) x y m = rshift x y m
  let ( asr ) x y m = arshift x y m
  let ( ++ ) x n m = nsucc x n m
  let ( -- ) x n m = npred x n m
end

module type S = sig
  type 'a m

  val bool : bool -> t
  val int : int -> t m
  val int32 : int32 -> t m
  val int64 : int64 -> t m
  val bigint : Z.t -> t m
  val zero : t
  val one : t
  val ones : t m
  val succ : t -> t m
  val nsucc : t -> int -> t m
  val pred : t -> t m
  val npred : t -> int -> t m
  val neg : t -> t m
  val lnot : t -> t m
  val abs : t -> t m
  val add : t -> t -> t m
  val sub : t -> t -> t m
  val mul : t -> t -> t m
  val div : t -> t -> t m
  val sdiv : t -> t -> t m
  val rem : t -> t -> t m
  val srem : t -> t -> t m
  val smod : t -> t -> t m
  val nth : t -> int -> bool m
  val msb : t -> bool m
  val lsb : t -> bool m
  val logand : t -> t -> t m
  val logor : t -> t -> t m
  val logxor : t -> t -> t m
  val lshift : t -> t -> t m
  val rshift : t -> t -> t m
  val arshift : t -> t -> t m
  val gcd : t -> t -> t m
  val lcm : t -> t -> t m
  val gcdext : t -> t -> (t * t * t) m
  val ( !$ ) : string -> t
  val ( !! ) : int -> t m
  val ( ~- ) : t -> t m
  val ( ~~ ) : t -> t m
  val ( + ) : t -> t -> t m
  val ( - ) : t -> t -> t m
  val ( * ) : t -> t -> t m
  val ( / ) : t -> t -> t m
  val ( /$ ) : t -> t -> t m
  val ( % ) : t -> t -> t m
  val ( %$ ) : t -> t -> t m
  val ( %^ ) : t -> t -> t m
  val ( land ) : t -> t -> t m
  val ( lor ) : t -> t -> t m
  val ( lxor ) : t -> t -> t m
  val ( lsl ) : t -> t -> t m
  val ( lsr ) : t -> t -> t m
  val ( asr ) : t -> t -> t m
  val ( ++ ) : t -> int -> t m
  val ( -- ) : t -> int -> t m
end

module type Modulus = sig
  val modulus : modulus
end

let to_string = Native.to_string
let of_string x = Native.of_string x |> invalid
let of_string_base b x = Native.of_string_base b x |> invalid
let defaults_to_length ?len x = match len with None -> String.length x | Some n -> n
let of_substring ?(pos = 0) ?len x =
  Native.of_string (String.sub x pos (defaults_to_length ?len x)) |> invalid
let of_substring_base ?(pos = 0) ?len b x =
  Native.of_string_base b (String.sub x pos (defaults_to_length ?len x)) |> invalid
let ( !$ ) x = of_string x
let ( !! ) x m = int x m
let fits_int x = Native.fits_int x Sys.int_size
let fits_int32 = Native.fits_int32
let fits_int64 = Native.fits_int64
let to_int x = Native.to_int x Sys.int_size |> fail
let to_int32 x = Native.to_int32 x |> fail
let to_int64 x = Native.to_int64 x |> fail

let bigarray_of_string input =
  let bytes = Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout (String.length input) in
  String.iteri (fun index value -> bytes.{index} <- Char.code value) input;
  bytes

let string_of_bigarray bytes =
  String.init (Bigarray.Array1.dim bytes) (fun index -> Char.chr bytes.{index})

let of_binary x = Native.of_binary (bigarray_of_string x) |> invalid
let to_binary x = string_of_bigarray (Native.to_binary x)
let pp ppf x = Format.fprintf ppf "%s" (to_string x)

module type D = S with type 'a m = 'a

module Make (M : Modulus) : D = struct
  type 'a m = 'a

  let m = M.modulus
  let bool x = bool x
  let int x = int x mod m
  let int32 x = int32 x mod m
  let int64 x = int64 x mod m
  let bigint x = bigint x mod m
  let zero = zero
  let one = one
  let ones = ones mod m
  let succ x = succ x mod m
  let nsucc x n = nsucc x n mod m
  let pred x = pred x mod m
  let npred x n = npred x n mod m
  let neg x = neg x mod m
  let lnot x = lnot x mod m
  let abs x = abs x mod m
  let add x y = add x y mod m
  let sub x y = sub x y mod m
  let mul x y = mul x y mod m
  let div x y = div x y mod m
  let sdiv x y = sdiv x y mod m
  let rem x y = rem x y mod m
  let srem x y = srem x y mod m
  let smod x y = smod x y mod m
  let nth x y = nth x y mod m
  let msb x = msb x mod m
  let lsb x = lsb x mod m
  let logand x y = logand x y mod m
  let logor x y = logor x y mod m
  let logxor x y = logxor x y mod m
  let lshift x y = lshift x y mod m
  let rshift x y = rshift x y mod m
  let arshift x y = arshift x y mod m
  let gcd x y = gcd x y mod m
  let lcm x y = lcm x y mod m
  let gcdext x y = gcdext x y mod m
  let ( !$ ) x = of_string x
  let ( !! ) x = int x
  let ( ~- ) x = neg x
  let ( ~~ ) x = lnot x
  let ( + ) x y = add x y
  let ( - ) x y = sub x y
  let ( * ) x y = mul x y
  let ( / ) x y = div x y
  let ( /$ ) x y = sdiv x y
  let ( % ) x y = rem x y
  let ( %$ ) x y = smod x y
  let ( %^ ) x y = srem x y
  let ( land ) x y = logand x y
  let ( lor ) x y = logor x y
  let ( lxor ) x y = logxor x y
  let ( lsl ) x y = lshift x y
  let ( lsr ) x y = rshift x y
  let ( asr ) x y = arshift x y
  let ( ++ ) x n = nsucc x n
  let ( -- ) x n = npred x n
end

module M1 = Make (struct let modulus = m1 end)
module M8 = Make (struct let modulus = m8 end)
module M16 = Make (struct let modulus = m16 end)
module M32 = Make (struct let modulus = m32 end)
module M64 = Make (struct let modulus = m64 end)

let modular : int -> (module D) = function
  | 1 -> (module M1)
  | 8 -> (module M8)
  | 16 -> (module M16)
  | 32 -> (module M32)
  | 64 -> (module M64)
  | n -> (module Make (struct let modulus = modulus n end))

include Syntax

let equal x y = compare x y = 0
let ( < ) x y = compare x y < 0
let ( > ) x y = compare x y > 0
let ( <= ) x y = compare x y <= 0
let ( >= ) x y = compare x y >= 0
let ( = ) x y = compare x y = 0
let ( <> ) x y = compare x y <> 0
