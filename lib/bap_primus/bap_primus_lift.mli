open Bap.Std

val max_size : int

val insn :
  ?disassembled_only:bool ->
  project ->
  read:(int64 -> int -> string) ->
  int64 ->
  (int * blk term list) option

val code : project -> int64 -> string option
