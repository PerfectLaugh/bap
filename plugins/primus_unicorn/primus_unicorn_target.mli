(** The correspondence between the targets of BAP and Unicorn. *)

open Bap_core_theory
open Bap.Std

val engine : Theory.Target.t -> (Bap_unicorn.arch * Bap_unicorn.Mode.t) option
(** [engine target] the architecture and mode of Unicorn that runs the code of
    [target], if Unicorn supports it. *)

val pc : Bap_unicorn.arch -> Bap_unicorn.Mode.t -> int
(** [pc arch mode] the program counter of Unicorn. *)

(** The registers of BAP in the registers of Unicorn.

    A register of BAP is either a whole register of Unicorn, a part of it, e.g.,
    a flag in the status register, or has no counterpart in Unicorn. The aliases
    of the registers of the target are their parts of the registers of their
    origins. *)
module Regs : sig
  type t

  val create : Theory.Target.t -> Bap_unicorn.arch -> Bap_unicorn.t -> t
  (** [create target arch uc] maps the registers of [target] to the registers of
      [uc]. *)

  val mem : t -> var -> bool
  (** [mem regs v] if [v] has a counterpart in Unicorn. *)

  val read : t -> var -> word option
  (** [read regs v] reads the value of [v] from Unicorn. *)

  val write : t -> var -> word -> bool
  (** [write regs v x] writes [x] to the counterpart of [v], if [v] has one,
      otherwise does nothing and returns [false]. *)

  val basis : t -> var list
  (** the mapped registers that are not aliases *)

  val unmapped : t -> string list
  (** the registers of the target that have no counterparts *)

  val read_name : t -> string -> word option
  (** [read_name regs name] reads the register of the target by its name. *)

  val write_name : t -> string -> word -> bool
  (** [write_name regs name x] writes [x], extended or truncated to the width of
      the register, if the register has a counterpart. *)

  val names : t -> string list
  (** the names of the registers that have counterparts *)
end
