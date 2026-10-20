(** The serialization of the terms of BIR in protobuf and JSON, see
    bap_protobuf_ir.proto. *)

open Bap.Std

type fmt = Bil_proto.fmt

val program_to_string : fmt -> program term -> string
val program_of_string : fmt -> string -> program term
val sub_to_string : fmt -> sub term -> string
val sub_of_string : fmt -> string -> sub term
val blk_to_string : fmt -> blk term -> string
val blk_of_string : fmt -> string -> blk term
val arg_to_string : fmt -> arg term -> string
val arg_of_string : fmt -> string -> arg term
val phi_to_string : fmt -> phi term -> string
val phi_of_string : fmt -> string -> phi term
val def_to_string : fmt -> def term -> string
val def_of_string : fmt -> string -> def term
val jmp_to_string : fmt -> jmp term -> string
val jmp_of_string : fmt -> string -> jmp term
