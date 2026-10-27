open Bap.Std

type operation = Add | Sub | And | Or | Xor
type state

val execute : Bil.t -> (state, string) result
val input : state -> string -> (Bil.exp, string) result
val output : state -> string -> (Bil.exp, string) result
val check_writes : expected:string list -> state -> (unit, string) result

val validate_reg_reg_with :
  checker:(string -> (unit, string) result) ->
  operation:operation ->
  width:int ->
  destination:string ->
  left:string ->
  right:string ->
  Bil.t ->
  (unit, string) result

val validate_reg_reg :
  operation:operation ->
  width:int ->
  destination:string ->
  left:string ->
  right:string ->
  Bil.t ->
  (unit, string) result
