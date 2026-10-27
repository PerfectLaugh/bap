open Bap.Std

type operation = Add | Sub | And | Or | Xor

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

val validate_add_with :
  checker:(string -> (unit, string) result) ->
  width:int ->
  Bil.t ->
  (unit, string) result

val validate_add : width:int -> Bil.t -> (unit, string) result
