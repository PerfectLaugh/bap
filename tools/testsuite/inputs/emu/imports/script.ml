#require "bap-primus-native.emu"

module Emu = Bap_emu

(* Prints the slots of the external functions, that the loader resolved,
   with the functions, to which they refer, when the program starts. *)

let print emu =
  List.iter
    (fun ({ name; value; _ } : Emu.import) ->
      Printf.printf "import %s -> %s\n" name
        (match Option.bind value (Emu.function_at emu) with
        | Some f -> f
        | None -> "?"))
    (Emu.imports emu)

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create (Bap_script.project file) in
  print emu
