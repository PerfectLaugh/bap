open Core

val statements :
  ?bookkeeping:String.Set.t ->
  Decompile_ast.stmt list ->
  Decompile_ast.stmt list

val used_variables : Decompile_ast.stmt list -> Int.Set.t
