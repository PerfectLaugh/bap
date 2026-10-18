(** The functional tests of bap and bap-mc.

    A test is a list of cases, each case runs the tools on the files of the
    testsuite repository and checks their outputs. The cases run in parallel,
    each in its own directory and with its own cache, state, configuration and
    log directories, so they don't see each other. *)

type data
(** the checkout of the testsuite repository *)

val data : string -> data
(** [data dir] is the testsuite checked out in [dir]. *)

val path : data -> string -> string
(** [path data name] is the absolute name of [name], a path relative to the root
    of the testsuite, e.g., ["bin/x86_64-linux-gnu-echo"]. *)

val files : data -> string -> (string -> bool) -> string list
(** [files data dir select] are the paths of the files of the directory [dir] of
    the testsuite, relative to its root and in the alphabetical order, whose
    names satisfy [select]. *)

type env
(** the environment of a running case *)

val dir : env -> string
(** [dir env] is the own directory of the case, which is the working directory
    of the commands that it runs. *)

val file : env -> string -> string
(** [file env name] is the absolute name of [name] in [dir env]. *)

val write : env -> string -> string -> string
(** [write env name data] writes [data] to [file env name] and returns its name.
*)

type status =
  | Exited of int  (** the command exited with the code *)
  | Signaled  (** the command was terminated by a signal *)
  | Timeout  (** the command was killed, since it ran out of time *)
  | Stopped  (** the command was killed, since its output matched *)

type output = { text : string; status : status }
(** the output of a command, both its standard output and error *)

val bap :
  ?timeout:float ->
  ?until:string ->
  ?env:(string * string) list ->
  env ->
  string list ->
  output
(** [bap env args] runs bap with the arguments [args].

    The command is killed after [timeout] seconds (600 by default) or as soon as
    its output matches the regular expression [until]. The variables [env] are
    added to the environment of the command. *)

val mc : env -> string list -> output
(** [mc env args] runs bap-mc with the arguments [args]. *)

val check : env -> string -> bool -> unit
(** [check env name ok] reports the check [name], which passed if [ok]. *)

val has : env -> string -> output -> string -> unit
(** [has env name output regexp] checks that [regexp] matches [output].

    The regular expressions are in the Perl syntax, in which [.] matches any
    character, including the new line. *)

val lacks : env -> string -> output -> string -> unit
(** [lacks env name output regexp] checks that [regexp] doesn't match [output].
*)

val contains : env -> string -> output -> string -> unit
(** [contains env name output str] checks that [str] is a substring of [output].
*)

val matches : output -> string -> bool
(** [matches output regexp] is [true] if [regexp] matches [output]. *)

val count : output -> string -> int
(** [count output str] is the number of the occurrences of [str] in [output],
    which don't overlap. *)

val sequence : env -> output -> (string * string) list -> unit
(** [sequence env output checks] checks that the regular expressions of the
    named [checks] match [output] in their order, i.e., each one matches after
    the end of the shortest match of the previous one. The checks stop at the
    first one that doesn't match. *)

type case
(** a case of a test *)

val case : ?serial:bool -> ?slow:bool -> string -> (env -> unit) -> case
(** [case name run] is the case [name], which is run by [run].

    The cases that are [serial] run alone, after the others, since they change
    the installation of bap, and the [slow] cases start first. An exception that
    [run] raises fails the case. *)

val main : (data -> case list) list -> unit
(** [main tests] runs the cases of [tests], which the command line selects, and
    exits with 1 if any of them fails. *)
