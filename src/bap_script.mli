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
  ?loader:string -> ?target:Bap_core_theory.Theory.Target.t -> string -> project
(** [project file] disassembles the [file], as the disassemble command does,
    with the [loader], llvm by default, and runs the passes that run
    automatically, e.g., api, without the cache of the knowledge. *)

val run_pass : string -> project -> project
(** [run_pass name project] runs the pass, e.g., ["run"], after its
    dependencies. *)

(**/**)

val set_args : string list -> unit
