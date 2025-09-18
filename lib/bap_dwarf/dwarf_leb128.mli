open Core
(** LEB128 - Little Endian Base 128 encoding. *)

type t [@@deriving bin_io, compare, sexp]
(** an encoded value *)

type 'a encoder = ?signed:bool -> 'a -> t
(** [encode ~signed v] encodes value [v] in a LEB128 format. If signed is true,
    then uses signed encoding. *)

type 'a decoder = t -> 'a Or_error.t
(** [decode leb] decodes a number from LEB128 representation. *)

val size : t -> int
(** [size leb] return size in bytes of the number stored in LEB128 encoding. *)

val read : ?signed:bool -> string -> pos_ref:int ref -> t Or_error.t
val write : t -> Bytes.t -> pos:int -> unit
val to_int : int decoder
val to_int32 : int32 decoder
val to_int64 : int64 decoder
val of_int : int encoder
val of_int32 : int32 encoder
val of_int64 : int64 encoder
