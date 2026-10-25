(** The scripts of BAP.

    [bap script [--cache-dir=DIR] FILE.ml ARG...] compiles the OCaml script
    [FILE.ml] to the native code, which is cached in [DIR], if it is specified,
    and runs it, with the libraries of BAP, and the libraries that its lines
    [#require "LIB,..."] name, e.g., [#require "bap-primus"].

    The script configures the analyses with the arguments of the functions, that
    it calls, not with the options of the command line, e.g.,

    {[
    let lisp = { Bap_script.paths = [ dir ]; features = [ "syscalls" ] } in
    let proj = Bap_script.project ~lisp file in
    Bap_script.run proj ~args:[ "hello" ]
    ]}

    The plugins of BAP are loaded, when the script first needs them, e.g., by
    {!project}, or before the script runs, if it requires libraries, as they may
    use the libraries of the plugins, e.g., [bap-primus-native.emu] uses the one
    of the primus-lisp plugin, whose options are its own, only if the plugin
    loads it. A script starts bap without the options of the command line, so
    the options of the plugins come from the environment, whose variable is the
    full name of the option in upper case, with [BAP_] before it and the dashes
    replaced by the underscores, e.g., [BAP_READ_SYMBOLS_FROM=FILE] for
    [--read-symbols-from=FILE], or from the configuration files, otherwise they
    have their defaults.

    See [docs/emulation.md] for the guide to the scripts and the emulator, see
    [Bap_emu]. *)

open Bap.Std
open Bap_primus.Std

val args : unit -> string list
(** [args ()] the arguments of the script, after its file *)

val init : unit -> unit
(** [init ()] loads the plugins of BAP, with their defaults, once, and does
    nothing afterwards. {!project} calls it, and the script calls it, when it
    needs the plugins before, e.g., the systems of Primus. *)

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
  ?disassemble:bool ->
  ?loader:string ->
  ?target:Bap_core_theory.Theory.Target.t ->
  ?api:string list ->
  ?lisp:lisp ->
  string ->
  project
(** [project file] loads the [file] with the [loader], llvm by default, and runs
    the passes that run automatically, e.g., api, without the cache of the
    knowledge. The disassembly and the lifting are skipped, for the executors
    that run the code natively, e.g., the [bap:unicorn-executor] system, which
    lifts only the code, that Primus interprets, on demand: the program contains
    only the subroutines of the named symbols of the file, and of the symbols,
    that the user provided, e.g., with [--read-symbols-from], whose names come
    first, or, if there are none, e.g., the file is stripped, the subroutines
    that the knowledge base finds, which scans the whole code. With
    [~disassemble:true] the [file] is disassembled and lifted, as the
    disassemble command does, e.g., for the [bap:legacy-main] system, which
    interprets the whole program, or for the analyses of the whole program. The
    api pass applies the api files of the folders [api] too, see
    [Bap_api.with_paths], e.g., the prototypes of the functions of a target, and
    the Primus machines, that run the program, load the [lisp] program, see
    [Primus.Lisp.Load.with_features]. *)

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
    default [bap:lifted-executor], or [bap:unicorn-executor], if the
    primus-lifted plugin isn't loaded, or [bap:legacy-main], if the plugins of
    the executors, which are licensed under GPL, aren't installed, with the
    [components] of the repository, e.g., [bap:debugger], from the [entry], by
    default the entry point of the program, or [_start], with the program
    arguments [args], without the name of the program, and the environment
    [envp], e.g., [["HOME=/root"]].

    The components of [init] run in the machine after the components of the
    system, before the program starts, e.g., the components of the script, that
    it doesn't register. Returns the project, as the program left it, and
    reports, if the program failed. *)

(**/**)

val set_args : string list -> unit
