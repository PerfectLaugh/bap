open Bap.Std

val validate_with :
  checker:(string -> (unit, string) result) ->
  Bil.t ->
  Bil.t ->
  (unit, string) result

val validate : Bil.t -> Bil.t -> (unit, string) result
val checked_fold_consts : Bil.t -> Bil.t
