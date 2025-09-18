(* Copyright (C) 2017 ForAllSecure, Inc. - All Rights Reserved. *)
open Core
(** The type of variables.

    @author Ivan Jager *)

module Type = X86_legacy_bil_type

(** The type for a variable identifier. The int should uniquely identify the
    variable. The string is to make it easier for humans to read. A variable's
    type is embedded in it. *)
type t = V of int * string * Type.typ [@@deriving sexp]

val newvar : string -> Type.typ -> t
(** [newvar s t] creates a fresh variable of type [t] and human readable string
    [s]. *)

val typ : t -> Type.typ
(** [typ v] returns the type of [v]. *)

val name : t -> string
(** [name v] returns the name of [v]. *)

type defuse = { defs : t list; uses : t list }
(** Variable definition and use type. *)

include Comparable.S with type t := t
include Hashable.S with type t := t
