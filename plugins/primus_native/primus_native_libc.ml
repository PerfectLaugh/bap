(* The functions of libc that run on the memory of Unicorn, instead of
   their Lisp stubs, see [Primus_native_executor].

   A function reads the memory and returns the bytes that it writes,
   which the executor checks and writes, so that it changes nothing, if
   it can't run, e.g., when it reads a page that is not copied yet. The
   functions follow the C standard, e.g., memcmp compares the bytes as
   unsigned, and copy the bytes one by one from the first, as the Lisp
   stubs do, e.g., memcpy of the overlapping ranges. *)

open Core

exception Missing of int64
(** the page of the address is not copied to Unicorn *)

exception Denied
(** the function can't run, so the Lisp stub runs instead, e.g., to raise the
    fault *)

type memory = {
  read : int64 -> int -> string;
      (** [read addr n] the [n] bytes from [addr], raises [Denied], if Primus
          would fault on any of them *)
  prefix : int64 -> int -> string;
      (** [prefix addr n] the bytes from [addr], at most [n], up to the first
          byte, on which Primus would fault *)
}

(* the taint of the bytes, that a function writes, as its Lisp stub
   propagates it, for the lifted engine, that propagates the taint
   itself, see [Primus_native_executor.Shadow]: copied from the source,
   byte by byte, from the first, as memcpy does, or as if the source is
   read first, as memmove does, of an argument, e.g., the byte of
   memset, or none, e.g., the terminator of strcpy *)
type taint =
  | Copy of { dst : int64; src : int64; n : int }
  | Move of { dst : int64; src : int64; n : int }
  | Fill of { dst : int64; n : int; arg : int }
  | Clean of { dst : int64; n : int }

type result = {
  writes : (int64 * string) list;
  value : int64;
  taints : taint list option;
      (** the taint of the writes, or [None], if the result is computed from the
          bytes, that the function reads, e.g., of memcmp *)
  returns : int option;  (** the argument, that the function returns *)
}

let computed ?(writes = []) value =
  { writes; value; taints = None; returns = None }

let page_size = 0x1000L
let page_of addr = Int64.(addr land lnot (page_size - 1L))

(* the largest size of the memory, that a function reads or writes,
   larger sizes are left to the Lisp stubs, which take forever anyway *)
let limit = 1 lsl 24

let size n =
  if Int64.(n < 0L || n > of_int limit) then raise Denied
  else Int64.to_int_exn n

(* the length of the string at [p], without the terminating zero, which
   may end before a byte, on which Primus would fault, as the Lisp stub
   reads the bytes up to the zero *)
let strlen mem p =
  let rec scan addr len =
    let chunk = Int64.(to_int_exn (page_of addr + page_size - addr)) in
    let data = mem.prefix addr chunk in
    match String.index data '\000' with
    | Some i -> len + i
    | None when String.length data < chunk -> raise Denied
    | None ->
        let len = len + chunk in
        if len > limit then raise Denied
        else scan Int64.(addr + of_int chunk) len
  in
  scan p 0

let overlap a n b m = Int64.(a < b + of_int m && b < a + of_int n)
let byte c = Char.of_int_exn (Int64.to_int_exn Int64.(c land 0xFFL))

let compare_bytes x y =
  let rec loop i =
    if i = String.length x then 0L
    else
      let c = Char.compare x.[i] y.[i] in
      if c < 0 then -1L else if c > 0 then 1L else loop (i + 1)
  in
  loop 0

let memset _ p c n =
  let n = size n in
  {
    writes = [ (p, String.make n (byte c)) ];
    value = p;
    taints = Some [ Fill { dst = p; n; arg = 1 } ];
    returns = Some 0;
  }

let copied d taints writes =
  { writes; value = d; taints = Some taints; returns = Some 0 }

(* the destination inside the source repeats the bytes before it *)
let memcpy mem d s n =
  let n = size n in
  if Int64.(s < d && d < s + of_int n) then begin
    let shift = Int64.(to_int_exn (d - s)) in
    let buf = Bytes.of_string (mem.read s (shift + n)) in
    for i = 0 to n - 1 do
      Bytes.set buf (shift + i) (Bytes.get buf i)
    done;
    copied d
      [ Copy { dst = d; src = s; n } ]
      [ (d, Bytes.To_string.sub buf ~pos:shift ~len:n) ]
  end
  else copied d [ Copy { dst = d; src = s; n } ] [ (d, mem.read s n) ]

let memmove mem d s n =
  let n = size n in
  copied d [ Move { dst = d; src = s; n } ] [ (d, mem.read s n) ]

let memcmp mem a b n =
  let n = size n in
  computed (compare_bytes (mem.read a n) (mem.read b n))

let memchr mem p c n =
  let data = mem.read p (size n) in
  let value =
    match String.index data (byte c) with
    | Some i -> Int64.(p + of_int i)
    | None -> 0L
  in
  computed value

let strlen' mem p = computed (Int64.of_int (strlen mem p))

(* compares the strings up to the first zero of either of them, and at
   most [n] bytes *)
let strncmp mem a b n =
  let la = strlen mem a and lb = strlen mem b in
  memcmp mem a b (Int64.min n (Int64.of_int (Int.min la lb + 1)))

let strcmp mem a b = strncmp mem a b (Int64.of_int limit)

(* the bytes of the string, whose terminator the stub writes itself *)
let copy_string mem d s =
  let n = strlen mem s + 1 in
  if overlap d n s n then raise Denied;
  ( (d, mem.read s n),
    [
      Copy { dst = d; src = s; n = n - 1 };
      Clean { dst = Int64.(d + of_int Int.(n - 1)); n = 1 };
    ] )

let strcpy mem d s =
  let write, taints = copy_string mem d s in
  copied d taints [ write ]

let strcat mem d s =
  let tail = Int64.(d + of_int (strlen mem d)) in
  let write, taints = copy_string mem tail s in
  copied d taints [ write ]

let strchr mem p c = memchr mem p c (Int64.of_int (strlen mem p + 1))

type fn = memory -> int64 list -> result

let unary f mem = function [ a ] -> f mem a | _ -> raise Denied
let binary f mem = function [ a; b ] -> f mem a b | _ -> raise Denied
let ternary f mem = function [ a; b; c ] -> f mem a b c | _ -> raise Denied

let functions : (string * fn) list =
  [
    ("memset", ternary memset);
    ("memcpy", ternary memcpy);
    ("memmove", ternary memmove);
    ("memcmp", ternary memcmp);
    ("memchr", ternary memchr);
    ("strlen", unary strlen');
    ("strcmp", binary strcmp);
    ("strcoll", binary strcmp);
    ("strncmp", ternary strncmp);
    ("strcpy", binary strcpy);
    ("strcat", binary strcat);
    ("strchr", binary strchr);
    ("index", binary strchr);
  ]

let names = List.map functions ~f:fst
let find name = List.Assoc.find functions name ~equal:String.equal
