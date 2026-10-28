open Bap.Std
open Bap_core_theory

val decompile :
  ?concise:bool ->
  target:Theory.Target.t ->
  ?memory:Bap.Std.value Bap.Std.memmap ->
  program term ->
  Decompile_ast.program
