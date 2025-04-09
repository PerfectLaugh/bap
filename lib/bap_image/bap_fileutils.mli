(**Helper IO functions. *)

open Core
open Bap_types.Std

val readfile : string -> Bigstring.t

val parse_name : string -> (string * string option) option
