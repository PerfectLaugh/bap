open Bap_core_theory
open Bap.Std

val thumb : unit -> Theory.language option
val a32 : unit -> Theory.language option
val encoding : thumb:bool -> Theory.language option
val is_thumb : Theory.language -> bool
val unmask : blk term list -> blk term list

val jump :
  name:string -> thumb:bool -> next:addr -> blk term list -> addr -> addr * bool
