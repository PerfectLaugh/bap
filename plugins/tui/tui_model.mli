open Core
open Bap.Std
open Bap_core_theory
open Regular.Std

type view =
  | Decompile
  | Disassembly
  | Bir
  | Cfg
  | Symbols
  | Memory
  | Info
  | Passes
  | Writers
  | Console
  | Help

type func = { tid : Tid.t; name : string; addr : Word.t option }

type state = {
  project : Project.t;
  file : string;
  concise : bool;
  view : view;
  functions : func list;
  selected : int;
  filter : string;
  scroll : int;
  memory_offset : int;
  console_output : string;
  status : string;
  recovered : (bool, Bap_decompile.Ast.program) Hashtbl.Poly.t;
}

val views : view list
val view_name : view -> string
val functions : Project.t -> func list
val create : ?concise:bool -> Project.t -> string -> state

val load :
  ?concise:bool ->
  ?loader:string ->
  ?target:Theory.Target.t ->
  string ->
  (state, Error.t) Result.t

val filtered : state -> func list
val selected : state -> func option
val select : state -> int -> state
val move : state -> int -> state
val set_view : state -> view -> state
val cycle_view : state -> int -> state
val set_filter : state -> string -> state
val select_address : state -> string -> state
val writer_text : Project.t -> string -> string
val decompile : state -> string
val bir : state -> string
val info : state -> string
val symbol_xrefs : state -> string
val passes : state -> string
val writers : state -> string
val memory : state -> string
val next_memory_region : state -> int -> state
val text : state -> string
val run_pass : state -> string -> (state, Error.t) Result.t
val command_args : state -> ?script:string -> string list -> string list
val decompiled_name : string -> string
