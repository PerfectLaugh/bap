open Bap_core_theory
open Theory
open Thumb_core
open Thumb_opcodes

type eff = cond -> unit effect_ KB.t

module Make (Core : Theory.Core) : sig
  val ldri : r32 reg -> r32 reg -> int -> eff
  (** [ldr rd, [rn, #i]] *)

  val ldrr : r32 reg -> r32 reg -> r32 reg -> eff
  (** [ldr rd, [rn, rm]] *)

  val ldrbi : r32 reg -> r32 reg -> int -> eff
  (** [ldrb rd, [rn, #i]] *)

  val ldrbr : r32 reg -> r32 reg -> r32 reg -> eff
  (** [ldrb rd, [rn, rm]] *)

  val ldrsb : r32 reg -> r32 reg -> r32 reg -> eff
  (** [ldrsb rd, [rn, rm]] *)

  val ldrhi : r32 reg -> r32 reg -> int -> eff
  (** [ldrh rd, [rn, #i]] *)

  val ldrhr : r32 reg -> r32 reg -> r32 reg -> eff
  (** [ldrh rd, [rn, rm]] *)

  val ldrsh : r32 reg -> r32 reg -> r32 reg -> eff
  (** [ldrsh rd, [rn, rm]] *)

  val ldrpci : r32 reg -> Bitvec.t -> int -> eff
  (** [ldr rd <label>] *)

  val ldm : r32 reg -> r32 reg list -> eff
  (** [ldm b!, {rm,...,rn}] *)

  val stri : r32 reg -> r32 reg -> int -> eff
  (** [str rd, [rm, #i]] *)

  val strr : r32 reg -> r32 reg -> r32 reg -> eff
  (** [str rd, [rm, rn]] *)

  val strhi : r32 reg -> r32 reg -> int -> eff
  (** [strh rd, [rm, #i]] *)

  val strhr : r32 reg -> r32 reg -> r32 reg -> eff
  (** [strh rd, [rm, rn]] *)

  val strbi : r32 reg -> r32 reg -> int -> eff
  (** [strb rd, [rm, #i]] *)

  val strbr : r32 reg -> r32 reg -> r32 reg -> eff
  (** [strb rd, [rm, rn]] *)

  val stm : r32 reg -> r32 reg list -> eff
  (** [stm b!, {rm,...,rn}] *)

  val pop : r32 reg list -> eff
  (** [pop {rm,...,rn}] *)

  val popret : r32 reg list -> eff
  (** [pop {rm,...,rn,pc}] *)

  val push : r32 reg list -> eff
  (** [push {rm,...,rn}] *)
end
