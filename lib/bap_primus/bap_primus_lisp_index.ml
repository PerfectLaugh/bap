open Core

module type S = sig
  type t [@@deriving sexp_of]

  val null : t
  val next : t -> t
  val pp : Format.formatter -> t -> unit
  val to_int : t -> int
  val of_int : int -> t

  include Comparable.S_plain with type t := t
end

module Make () : S = struct
  let null = Int63.zero
  let next = Int63.succ

  include Int63

  let to_int = Int63.to_int_exn
  let of_int = Int63.of_int
end

type ('a, 'i, 'e) interned = { data : 'a; id : 'i; eq : 'e }
