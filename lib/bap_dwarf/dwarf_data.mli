open Core
(** Representation for Dwarf Data. *)

open Bap.Std
open Dwarf_types

type 'a t
type 'a buffer

(** Buffer is a light abstraction over [string] and [bigstring], that can allow
    one to share the same string for different sections without explicit
    copying. *)
module Buffer : sig
  type 'a t = 'a buffer

  val create : ?pos:int -> 'a -> 'a t
  (** [create ~pos:0 ] creates a buffer from a data *)

  val with_pos : 'a t -> int -> 'a t
  (** [with_pos buf pos] creates a new buffer that shares data with [buf], but
      has different starting position *)

  val with_off : 'a t -> int -> 'a t
  (** [with_off buf off] creates a new buffer that shares data with [buf], but
      has different starting position equal to [pos buf + off] *)

  val pos : 'a t -> int
  (** [pos buf] starting position *)

  val data : 'a t -> 'a
  (** [data pos] actual data.

      Note: it doesn't start from [pos], it start from [0] *)
end

val create : endian -> (section * 'a buffer) list -> 'a t Or_error.t
(** [create endian sections] creates data representation from a assoc list of
    sections. Will complain if there're repeating sections. *)

val section : 'a t -> section -> 'a buffer Or_error.t
(** [section data] lookups for a [section] in [data] *)

val endian : 'a t -> endian
(** [endian data] the endianness of [data] *)
