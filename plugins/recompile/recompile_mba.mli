open Core
open Bap.Std

val simplify_exp_with :
  ?max_iterations:int ->
  ?max_rewrites:int ->
  validate:(exp -> exp -> (unit, string) result) ->
  exp ->
  exp Or_error.t

val simplify_exp :
  ?max_iterations:int -> ?max_rewrites:int -> exp -> exp Or_error.t

val simplify_exp_checked :
  ?max_iterations:int -> ?max_rewrites:int -> exp -> exp Or_error.t

val simplify_blk_with :
  ?max_iterations:int ->
  ?max_rewrites:int ->
  validate:(exp -> exp -> (unit, string) result) ->
  ?validate_propagation:
    (assumptions:(var * exp) list -> exp -> exp -> (unit, string) result) ->
  blk term ->
  blk term Or_error.t

val simplify_blk :
  ?max_iterations:int -> ?max_rewrites:int -> blk term -> blk term Or_error.t

val simplify_blk_checked :
  ?max_iterations:int -> ?max_rewrites:int -> blk term -> blk term Or_error.t

val simplify_with :
  ?max_iterations:int ->
  ?max_rewrites:int ->
  validate:(exp -> exp -> (unit, string) result) ->
  ?validate_propagation:
    (assumptions:(var * exp) list -> exp -> exp -> (unit, string) result) ->
  sub term ->
  sub term Or_error.t

val simplify :
  ?max_iterations:int -> ?max_rewrites:int -> sub term -> sub term Or_error.t

val simplify_checked :
  ?max_iterations:int -> ?max_rewrites:int -> sub term -> sub term Or_error.t
