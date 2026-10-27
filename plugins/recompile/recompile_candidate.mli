open Core
open Bap.Std

val validate_candidate : sub term -> sub term -> (unit, Error.t) result
