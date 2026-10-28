open Bap.Std
open Bap_core_theory

val decompile :
  ?concise:bool ->
  target:Theory.Target.t ->
  program term ->
  Decompile_ast.program
