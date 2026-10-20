(** The scripts of BAP.

    [bap script FILE.ml ARG...] compiles the OCaml script [FILE.ml] to the
    native code and runs it, with the libraries of BAP, and the libraries that
    its lines [#require "LIB,..."] name, e.g., [#require "bap-primus"].

    The script starts BAP with {!init}, with the options of the command line,
    e.g., [["--primus-unicorn-timeout=90"]], which it may compute, and then uses
    the API of BAP, e.g., {!project} and {!run_pass}. *)

open Bap.Std

val args : unit -> string list
(** [args ()] the arguments of the script, after its file *)

val init : ?options:string list -> unit -> unit
(** [init ~options ()] loads the plugins, and configures them with the
    [options], which are the options of the command line of bap, e.g.,
    ["--run-systems=bap:unicorn-executor"]. Exits, if the options are wrong. It
    may be called once, and {!project} calls it without the options, if the
    script did not. *)

val project :
  ?bare:bool ->
  ?loader:string ->
  ?target:Bap_core_theory.Theory.Target.t ->
  string ->
  project
(** [project file] disassembles the [file], as the disassemble command does,
    with the [loader], llvm by default, and runs the passes that run
    automatically, e.g., api, without the cache of the knowledge. With
    [~bare:true] the disassembly and the lifting are skipped: the program
    contains only the subroutines that the knowledge base knows, e.g., from
    --read-symbols-from, for the executors that run the code natively, e.g., the
    [bap:unicorn-executor] system. *)

val run_pass : string -> project -> project
(** [run_pass name project] runs the pass, e.g., ["run"], after its
    dependencies. *)

val require_options : string list -> unit
(** [require_options options] adds the [options] to the options of {!init},
    which a library of the scripts, e.g., the debugger, requires. It must be
    called before {!init}, e.g., when the library is loaded. *)

(**/**)

val set_args : string list -> unit
