open Bap.Std
open Bap_core_theory

val max_size : int

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
