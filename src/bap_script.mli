(** The scripts of BAP.

    [bap script [--cache-dir=DIR] FILE.ml ARG...] compiles the OCaml script
    [FILE.ml] to the native code, which is cached in [DIR], if it is specified,
    and runs it, with the libraries of BAP, and the libraries that its lines
    [#require "LIB,..."] name, e.g., [#require "bap-primus"].

    The script configures the analyses with the arguments of the functions, that
    it calls, not with the options of the command line, e.g.,

    {[
    let lisp = { Bap_script.paths = [ dir ]; features = [ "syscalls" ] } in
    let proj = Bap_script.project ~bare:true ~lisp file in
    Bap_script.run proj ~system:"bap:unicorn-executor" ~args:[ "hello" ]
    ]}

    The plugins of BAP are loaded with their defaults, when the script first
    needs them, e.g., by {!project}. *)

open Bap.Std
open Bap_primus.Std

val args : unit -> string list
(** [args ()] the arguments of the script, after its file *)

val init : unit -> unit
(** [init ()] loads the plugins of BAP, with their defaults, once, and does
    nothing afterwards. {!project} and {!run} call it, and the script calls it,
    when it needs the plugins before, e.g., the systems of Primus. *)

type lisp = {
  paths : string list;
      (** the folders, that are searched for the features first *)
  features : string list;
      (** the features, e.g., [syscalls], or their files, e.g.,
          [dir/syscalls.lisp], whose folders are searched first *)
}
(** the Primus Lisp program, that the machine loads, besides the features of the
    library, e.g., [posix] *)

val project :
  ?bare:bool ->
  ?loader:string ->
  ?target:Bap_core_theory.Theory.Target.t ->
  ?api:string list ->
  ?lisp:lisp ->
  string ->
  project
(** [project file] disassembles the [file], as the disassemble command does,
    with the [loader], llvm by default, and runs the passes that run
    automatically, e.g., api, without the cache of the knowledge. With
    [~bare:true] the disassembly and the lifting are skipped: the program
    contains only the subroutines that the knowledge base knows, e.g., from the
    symbols of the file, for the executors that run the code natively, e.g., the
    [bap:unicorn-executor] system. The api pass applies the api files of the
    folders [api] too, see [Bap_api.with_paths], e.g., the prototypes of the
    functions of a target, and the Primus machines, that run the program, load
    the [lisp] program, see [Primus.Lisp.Load.with_features]. *)

val run_pass : string -> project -> project
(** [run_pass name project] runs the pass, e.g., ["api"], after its
    dependencies. *)

val run :
  ?system:string ->
  ?components:string list ->
  ?init:Primus.Machine.component list ->
  ?args:string list ->
  ?envp:string list ->
  ?entry:string ->
  project ->
  project
(** [run project] runs the program of the [project] in the Primus [system], by
    default [bap:legacy-main], with the [components] of the repository, e.g.,
    [bap:debugger], from the [entry], by default the entry point of the program,
    or [_start], with the program arguments [args], without the name of the
    program, and the environment [envp], e.g., [["HOME=/root"]].

    The components of [init] run in the machine after the components of the
    system, before the program starts, e.g., the components of the script, that
    it doesn't register. Returns the project, as the program left it, and
    reports, if the program failed. *)

(**/**)

val set_args : string list -> unit
