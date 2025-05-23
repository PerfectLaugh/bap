(** Extends [Bitvector] module with extra functions.

    Fields of this structure will be added to an [Addr] module exposed
    in standard interface module [Std].

    This is a place, where we can add functions to a bitvector
    interface, that corresponds mostly to using bitvectors as a
    representation of an address.
*)

open Core
open Bap_common_types
val memref : ?disp:int -> ?index:int -> ?scale:size -> addr -> addr

(** Address arithmetic  *)
module type Arith = sig
  include Integer
  val create : addr -> t Or_error.t
end

(** Arithmetic on 32-bit addresses *)
module R32 : Arith with type t = int32

(** Arithmetic on 64-bit addresses  *)
module R64 : Arith with type t = int64
