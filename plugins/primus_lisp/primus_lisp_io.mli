open Bap_primus.Std

val standard_channels : string list
val init : (string * string) list -> unit

val redirect : (string * string) list -> Primus.Machine.component
(** [redirect redirections] the component, that redirects the channels of the
    machine, e.g., [("<stdin>", "input.txt")], instead of the redirections of
    the options *)
