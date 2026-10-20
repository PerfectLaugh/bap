(** The serialization of BIL in protobuf and JSON, see bap_protobuf_ir.proto. *)

open Bap.Std

type fmt = [ `pb | `json ] [@@deriving sexp, enumerate]
(** the formats: the binary protobuf, and its JSON *)

val exp_to_string : fmt -> exp -> string
val exp_of_string : fmt -> string -> exp
val stmt_to_string : fmt -> stmt -> string
val stmt_of_string : fmt -> string -> stmt
val bil_to_string : fmt -> bil -> string
val bil_of_string : fmt -> string -> bil

(** {2 The messages} *)

val exp_to_proto : exp -> Bap_protobuf_ir.expr
val exp_of_proto : Bap_protobuf_ir.expr -> exp
val var_to_proto : var -> Bap_protobuf_ir.var
val var_of_proto : Bap_protobuf_ir.var -> var

(** {2 The codecs} *)

val encode :
  fmt ->
  ('a -> Pbrt.Encoder.t -> unit) ->
  ('a -> Yojson.Basic.t) ->
  'a ->
  string
(** [encode fmt encode_pb encode_json message] is [message] in [fmt]. *)

val decode :
  fmt -> (Pbrt.Decoder.t -> 'a) -> (Yojson.Basic.t -> 'a) -> string -> 'a
(** [decode fmt decode_pb decode_json data] is the message of [data] in [fmt].
*)

val required : string -> 'a option -> 'a
(** [required what field] is the value of the [field] of a message, which is
    [what], and fails, if the message has no such field. *)
