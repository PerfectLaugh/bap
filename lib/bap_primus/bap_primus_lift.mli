open Bap.Std

val max_size : int

val insn :
  ?disassembled_only:bool ->
  ?encoding:Bap_core_theory.Theory.language ->
  project ->
  read:(int64 -> int -> string) ->
  int64 ->
  (int * blk term list) option

val code : project -> int64 -> string option
val encoding : project -> int64 -> Bap_core_theory.Theory.language option
val name : project -> int64 -> string option
