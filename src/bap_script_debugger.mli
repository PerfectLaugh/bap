(** The debugger of the scripts.

    [#require "bap-frontend.script-debugger"] adds the component of the debugger
    to the systems that the script runs, which stops the machines at the
    breakpoints, or at every instruction, while stepping, see
    [Primus.Interpreter.Stops], and calls the handlers of the script, which see
    and change the machine with the API of Primus.

    The handlers change the registers with [Primus.Interpreter.Make.set] and the
    memory with [Primus.Interpreter.Make.store], so that the executors that copy
    the state, e.g., Unicorn, see the changes. *)

open Bap.Std
open Bap_primus.Std

val break : string -> unit
(** [break point] stops the machines at the address or the subroutine with the
    name [point], which is resolved, when the first machine starts. *)

val step : bool -> unit
(** [step on] stops the machines at every instruction, while [on]. *)

(** the handler of the stops *)
module type Handler = functor (Machine : Primus.Machine.S) -> sig
  val stopped : addr -> unit Machine.t
  (** [stopped addr] is called, when the machine stops at [addr] *)
end

val on_stop : (module Handler) -> unit
(** [on_stop handler] calls the [handler] at the stops, after the handlers that
    were added before it. *)
