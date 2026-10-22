(* The formatting of printf, which the stubs of the functions of the
   printf family share, see stdio.lisp, of the words, that the C ABI
   passes, so the floating point values, which it passes in the other
   registers, e.g., the XMM registers of x86-64, are not formatted, and
   their conversions, e.g., %f, are output as they are. *)

open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std

type spec = {
  left : bool;  (** - *)
  zero : bool;  (** 0 *)
  plus : bool;  (** + *)
  space : bool;  (** the space *)
  alt : bool;  (** # *)
  width : int option;
  precision : int option;
  bits : int option;  (** of the length modifier, e.g., l *)
}

let blank =
  {
    left = false;
    zero = false;
    plus = false;
    space = false;
    alt = false;
    width = None;
    precision = None;
    bits = None;
  }

(* the field of the [width], aligned and padded as [spec] tells, where
   [prefix], e.g., the sign or 0x, precedes the zeros *)
let pad spec ?(prefix = "") ?(numeric = false) body =
  let len = String.length prefix + String.length body in
  match spec.width with
  | Some width when width > len ->
      let fill = width - len in
      if spec.left then prefix ^ body ^ String.make fill ' '
      else if spec.zero && numeric && Option.is_none spec.precision then
        prefix ^ String.make fill '0' ^ body
      else String.make fill ' ' ^ prefix ^ body
  | _ -> prefix ^ body

(* the digits of the integer, at least [precision] of them *)
let digits spec base ~upper x =
  let s =
    match base with
    | 8 -> Z.format "%o" x
    | 16 -> if upper then Z.format "%X" x else Z.format "%x" x
    | _ -> Z.to_string x
  in
  match spec.precision with
  | Some 0 when Z.equal x Z.zero -> ""
  | Some p when p > String.length s -> String.make (p - String.length s) '0' ^ s
  | _ -> s

module Make (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Eval = Primus.Interpreter.Make (Machine)
  module Value = Primus.Value.Make (Machine)

  let width = Machine.gets Project.target >>| Theory.Target.bits

  let byte ptr =
    Eval.load ptr LittleEndian `r8 >>| fun c ->
    Char.of_int_exn (Word.to_int_exn (Value.to_word c))

  (* the string at [ptr], at most [limit] bytes of it *)
  let string ?limit ptr =
    let buf = Buffer.create 16 in
    let rec loop ptr n =
      match limit with
      | Some limit when n >= limit -> Machine.return (Buffer.contents buf)
      | _ ->
          byte ptr >>= fun c ->
          if Char.(c = '\000') then Machine.return (Buffer.contents buf)
          else (
            Buffer.add_char buf c;
            Value.succ ptr >>= fun ptr -> loop ptr (n + 1))
    in
    loop ptr 0

  (* the words of the arguments, that the conversions take in order *)
  type args = { mutable rest : Value.t list }

  let next args =
    match args.rest with
    | [] -> None
    | x :: xs ->
        args.rest <- xs;
        Some (Value.to_word x)

  (* the integer of [bits], which may take two words, e.g., long long on
     x86, the lower one first *)
  let integer args ~word bits ~signed =
    let value =
      if bits > word then
        match (next args, next args) with
        | Some lo, Some hi -> Some (Word.concat hi lo)
        | Some lo, None -> Some lo
        | None, _ -> None
      else next args
    in
    Option.map value ~f:(fun x ->
        let bits = Int.min bits (Word.bitwidth x) in
        let x = Word.extract_exn ~hi:(bits - 1) x in
        let x = if signed then Word.signed x else x in
        Bitvec.to_bigint (Word.to_bitvec x) |> fun z ->
        if signed && Word.(is_negative x) then Z.sub z (Z.shift_left Z.one bits)
        else z)

  let signed spec x =
    let sign =
      if Z.lt x Z.zero then "-"
      else if spec.plus then "+"
      else if spec.space then " "
      else ""
    in
    pad spec ~numeric:true ~prefix:sign (digits spec 10 ~upper:false (Z.abs x))

  let unsigned spec base ~upper x =
    let body = digits spec base ~upper x in
    let prefix =
      if not spec.alt then ""
      else
        match base with
        | 16 when not (Z.equal x Z.zero) -> if upper then "0X" else "0x"
        | 8 when not (String.is_prefix body ~prefix:"0") -> "0"
        | _ -> ""
    in
    pad spec ~numeric:true ~prefix body

  (* the length modifier, e.g., hh, l, or z, in bits *)
  let length fmt i ~word =
    let at j = if j < String.length fmt then Some fmt.[j] else None in
    match (at i, at (i + 1)) with
    | Some 'h', Some 'h' -> (Some 8, i + 2)
    | Some 'l', Some 'l' -> (Some 64, i + 2)
    | Some 'h', _ -> (Some 16, i + 1)
    | Some ('l' | 'z' | 'j' | 't'), _ -> (Some word, i + 1)
    | Some ('q' | 'L'), _ -> (Some 64, i + 1)
    | _ -> (None, i)

  (* the output of the format at [fmt] with the words of [args] *)
  let format fmt args =
    width >>= fun word ->
    string fmt >>= fun fmt ->
    let args = { rest = args } in
    let out = Buffer.create (String.length fmt) in
    let n = String.length fmt in
    let at i = if i < n then Some fmt.[i] else None in
    let rec number i acc =
      match at i with
      | Some ('0' .. '9' as c) ->
          number (i + 1) ((acc * 10) + Char.to_int c - Char.to_int '0')
      | _ -> (acc, i)
    in
    (* the width or the precision, from the format or an argument *)
    let amount i =
      match at i with
      | Some '*' ->
          let x = Option.value_map (next args) ~default:0 ~f:Word.to_int_exn in
          (Some x, i + 1)
      | Some '0' .. '9' ->
          let x, i = number i 0 in
          (Some x, i)
      | _ -> (None, i)
    in
    let rec flags spec i =
      match at i with
      | Some '-' -> flags { spec with left = true } (i + 1)
      | Some '0' -> flags { spec with zero = true } (i + 1)
      | Some '+' -> flags { spec with plus = true } (i + 1)
      | Some ' ' -> flags { spec with space = true } (i + 1)
      | Some '#' -> flags { spec with alt = true } (i + 1)
      | _ -> (spec, i)
    in
    let int_bits spec = Option.value spec.bits ~default:32 in
    let rec loop i =
      if i >= n then Machine.return (Buffer.contents out)
      else if Char.(fmt.[i] <> '%') then (
        Buffer.add_char out fmt.[i];
        loop (i + 1))
      else
        let start = i in
        let spec, i = flags blank (i + 1) in
        let width, i = amount i in
        let spec =
          match width with
          | Some w when w < 0 -> { spec with left = true; width = Some (-w) }
          | width -> { spec with width }
        in
        let spec, i =
          match at i with
          | Some '.' -> (
              let precision, i = amount (i + 1) in
              match precision with
              | Some p when p < 0 -> (spec, i)
              | precision ->
                  ( {
                      spec with
                      precision = Some (Option.value precision ~default:0);
                    },
                    i ))
          | _ -> (spec, i)
        in
        let bits, i = length fmt i ~word in
        let spec = { spec with bits } in
        let emit s =
          Buffer.add_string out s;
          loop (i + 1)
        in
        let integer ~signed k =
          match integer args ~word (int_bits spec) ~signed with
          | Some x -> emit (k x)
          | None -> emit ""
        in
        match at i with
        | Some '%' -> emit "%"
        | Some ('d' | 'i') -> integer ~signed:true (signed spec)
        | Some 'u' -> integer ~signed:false (unsigned spec 10 ~upper:false)
        | Some 'o' -> integer ~signed:false (unsigned spec 8 ~upper:false)
        | Some 'x' -> integer ~signed:false (unsigned spec 16 ~upper:false)
        | Some 'X' -> integer ~signed:false (unsigned spec 16 ~upper:true)
        | Some 'c' -> (
            match next args with
            | Some x ->
                let c =
                  Char.of_int_exn (Word.to_int_exn (Word.extract_exn ~hi:7 x))
                in
                emit (pad spec (String.of_char c))
            | None -> emit "")
        | Some 'p' -> (
            match next args with
            | Some x when Word.is_zero x -> emit (pad spec "(nil)")
            | Some x ->
                let x = Bitvec.to_bigint (Word.to_bitvec x) in
                emit (pad spec ~prefix:"0x" (Z.format "%x" x))
            | None -> emit "")
        | Some 's' -> (
            match next args with
            | Some x when Word.is_zero x -> emit (pad spec "(null)")
            | Some x ->
                Value.of_word x >>= fun ptr ->
                string ?limit:spec.precision ptr >>= fun s -> emit (pad spec s)
            | None -> emit "")
        | Some 'n' ->
            ignore (next args : word option);
            loop (i + 1)
        | Some _ -> emit (String.sub fmt ~pos:start ~len:(i - start + 1))
        | None ->
            Buffer.add_string out (String.drop_prefix fmt start);
            Machine.return (Buffer.contents out)
    in
    loop 0
end
