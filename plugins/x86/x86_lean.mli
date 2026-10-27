open Bap.Std

val validate_add_with :
  checker:(string -> (unit, string) result) ->
  width:int ->
  Bil.t ->
  (unit, string) result

val validate_add : width:int -> Bil.t -> (unit, string) result
