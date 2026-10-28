open Bap.Std

val structure :
  Decompile_cfg.t ->
  block:(blk term -> Decompile_ast.stmt list) ->
  edge:(Decompile_cfg.edge -> Decompile_ast.stmt list) ->
  call:(jmp term -> Decompile_ast.stmt list) ->
  condition:(Tid.t -> exp -> Decompile_ast.expression) ->
  Decompile_ast.stmt list
