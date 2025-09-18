open Bap_core_theory
open Theory
open Thumb_core
open Thumb_opcodes

type eff = unit effect_ KB.t

module Make (CT : Theory.Core) : sig
  val b : Bitvec.t -> int -> eff
  (** [b <label>] *)

  val bcc : Bitvec.t -> cond -> int -> eff
  (** [bcc <label>] *)

  val bli : Bitvec.t -> int -> eff
  (** [bl <label>] *)

  val blxi : Bitvec.t -> int -> eff
  (** [blx <label>] *)

  val blxr : Bitvec.t -> r32 reg -> eff
  (** [blx rm] *)

  val bxr : r32 reg -> eff
  (** [bx rm] *)

  val bxi : Bitvec.t -> int -> eff
  (** [bx <label>] *)

  val blr : Bitvec.t -> r32 reg -> eff
  (** [bl rm] or [blx rm] *)

  val cbnz : Bitvec.t -> r32 reg -> int -> eff
  (** [cbnz rm <label>] *)

  val cbz : Bitvec.t -> r32 reg -> int -> eff
  (** [cbz rm <label>] *)
end
