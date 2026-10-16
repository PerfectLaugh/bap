(** The tables of facts discovered by the native loader.

    The native loader describes a file with named tables of rows, e.g., the
    [llvm:section-entry] table has a row per section, and passes them in a
    binary form (see [llvm_loader_utils.hpp]). The fields of the rows are read
    in place, without being copied or parsed. *)

open Core

type t

(** the type of a field *)
type typ = Int | Bool | Str

val of_bigstring : Bigstring.t -> t Or_error.t
(** [of_bigstring data] decodes the tables and checks that they are well formed.
*)

type table

val table : t -> string -> typ list -> table Or_error.t
(** [table doc name types] is the table [name] with the fields of the given
    [types]. A table that the loader didn't produce is empty, a table with
    different fields is an error. *)

val name : table -> string
val length : table -> int

val int : table -> int -> int -> int64
(** [int table row field] the value of an integer field *)

val bool : table -> int -> int -> bool
(** [bool table row field] the value of a boolean field *)

val str : table -> int -> int -> string
(** [str table row field] the value of a string field *)

val facts : table -> int list
(** [facts table] the indices of the distinct rows, the last added first.

    This is the order in which the facts of a document were enumerated when the
    tables were represented as Ogre attributes, which removed the duplicates,
    and the facts that are derived from the rows are provided in this order to
    preserve the order of the facts of the image specification. *)

val names : t -> string list
(** the names of the tables, in the order of their appearance *)
