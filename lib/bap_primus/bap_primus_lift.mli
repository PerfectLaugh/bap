open Bap.Std
open Bap_core_theory

val max_size : int

val instruction :
  ?encoding:Theory.language ->
  ?disassembled:bool ->
  project ->
  int64 ->
  string ->
  (int * blk term list) option KB.t

val named :
  ?encoding:Theory.language ->
  project ->
  int64 ->
  string ->
  (int * string * blk term list) option KB.t

val block :
  ?encoding:Theory.language ->
  budget:int ->
  count:int ->
  project ->
  int64 ->
  string ->
  (int * Theory.language * string * blk term list) list KB.t

val undefined :
  ?encoding:Theory.language -> project -> int64 -> string -> string option KB.t

module Make (Machine : Bap_primus_types.Machine) : sig
  val insn :
    ?disassembled_only:bool ->
    ?encoding:Theory.language ->
    read:(int64 -> int -> string) ->
    int64 ->
    (int * blk term list) option Machine.t

  val code : int64 -> string option Machine.t
  val encoding : int64 -> Theory.language option Machine.t
  val name : int64 -> string option Machine.t
end
