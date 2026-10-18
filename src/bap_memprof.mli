(* samples the live allocations when BAP_MEMPROF is set, see the module *)

val start : unit -> unit
(** [start ()] starts the sampling, if BAP_MEMPROF is the sampling rate. *)
