open Bap.Std

val check : string -> (unit, string) result

val validate_with :
  checker:(string -> (unit, string) result) ->
  Bil.t ->
  Bil.t ->
  (unit, string) result

val validate_application_with :
  checker:(string -> (unit, string) result) ->
  imports:string list ->
  function_name:string ->
  projection:string option ->
  unfold:string list ->
  Bil.exp ->
  Bil.exp list ->
  (unit, string) result

val validate_application :
  imports:string list ->
  function_name:string ->
  projection:string option ->
  unfold:string list ->
  Bil.exp ->
  Bil.exp list ->
  (unit, string) result

val validate : Bil.t -> Bil.t -> (unit, string) result
val checked_fold_consts : Bil.t -> Bil.t
