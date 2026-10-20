(** The benchmarks, that run in Eio, which measures them with its monotonic
    clock: each test runs for its quota of time, in batches, that double, and
    its time is the mean time of one run. *)

type t
(** a test, or a group of tests *)

val create : name:string -> (unit -> 'a) -> t
(** [create ~name f] the test [name], that runs [f ()] *)

val create_indexed : name:string -> args:int list -> (int -> unit -> 'a) -> t
(** [create_indexed ~name ~args f] the tests [name:n], that run [f n ()], for
    each [n] of [args] *)

val create_group : name:string -> t list -> t
(** [create_group ~name tests] the [tests], whose names have the prefix [name/]
*)

val run :
  clock:_ Eio.Time.Mono.t ->
  ?quota:Mtime.Span.t ->
  ?only:string list ->
  t list ->
  unit
(** [run ~clock tests] runs the [tests], whose names contain one of [only], by
    default all of them, for the [quota] of time each, by default half a second,
    and prints their mean times. *)
