open Core

type ('a, 'i, 'e) interned = { data : 'a; id : 'i; eq : 'e }

module type S = sig
  type t [@@deriving sexp_of]

  val null : t
  val next : t -> t
  val pp : Format.formatter -> t -> unit

  val to_int : t -> int
  (** [to_int x] the number of [x], e.g., to store it, see {!of_int} *)

  val of_int : int -> t

  include Comparable.S_plain with type t := t
end

module Make () : S
