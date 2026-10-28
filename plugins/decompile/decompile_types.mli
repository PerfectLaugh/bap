open Bap.Std
open Bap_core_theory

type t

type parameter = {
  name : string;
  var : var;
  typ : Decompile_ast.typ;
  location : exp;
}

type return_location = {
  var : var;
  field : string;
  offset : int;
  typ : Decompile_ast.typ;
}

val infer : target:Theory.Target.t -> program term -> t
val typ : t -> sub term -> var -> Decompile_ast.typ
val expression : t -> sub term -> exp -> Decompile_ast.typ
val signature : t -> sub term -> Decompile_ast.signature
val parameters : t -> sub term -> parameter list
val return_register : Theory.Target.t -> sub term -> var option
val return_locations : t -> sub term -> return_location list
val return_structure_name : sub term -> string
val structures : t -> Decompile_ast.structure list
val address : exp -> (var * int) option
val structure_name : sub term -> var -> string
