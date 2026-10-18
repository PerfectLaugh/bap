(* The line editor of the systems that have no linenoise, e.g., Windows,
   which reads lines without editing, history, completions, or hints. It
   has the subset of the interface of LNoise that analyze uses. *)

type completions = unit
type hint_color = Red | Green | Yellow | Blue | Magenta | Cyan | White

let clear_screen () =
  print_string "\027[2J\027[H";
  flush stdout

let history_load ~filename:_ = Ok ()
let history_add _ = Ok ()
let history_save ~filename:_ = Ok ()
let add_completion () _ = ()
let set_completion_callback (_ : string -> completions -> unit) = ()

let set_hints_callback (_ : string -> (string * hint_color * bool) option) =
  ()

let linenoise prompt =
  print_string prompt;
  flush stdout;
  try Some (input_line stdin) with End_of_file -> None
