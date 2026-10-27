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

val validate_assumptions_with :
  checker:(string -> (unit, string) result) ->
  assumptions:(Bil.var * Bil.exp) list ->
  Bil.exp ->
  Bil.exp ->
  (unit, string) result

val validate_assumptions :
  assumptions:(Bil.var * Bil.exp) list ->
  Bil.exp ->
  Bil.exp ->
  (unit, string) result
(** Proves an expression equivalence using prior variable definitions as
    equality premises, e.g., for copy propagation. *)

val validate_exp_exact_with :
  checker:(string -> (unit, string) result) ->
  Bil.exp ->
  Bil.exp ->
  (unit, string) result

val validate_exp_exact : Bil.exp -> Bil.exp -> (unit, string) result
(** Proves the two complete pure expressions equivalent without decomposing
    matching constructors into separate obligations. *)

val validate_exp : Bil.exp -> Bil.exp -> (unit, string) result
(** Checks changed pure subexpressions while preserving the surrounding
    expression structure, including memory and let-bound expressions. *)

val validate : Bil.t -> Bil.t -> (unit, string) result
val checked_fold_consts : Bil.t -> Bil.t
