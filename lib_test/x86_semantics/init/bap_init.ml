(* loads the plugins in a library without expect tests, as the plugins can't
   be loaded while the module of expect tests is initialized *)

let () =
  match Bap_main.init () with
  | Ok () -> ()
  | Error err ->
      Format.kasprintf failwith "Failed to initialize BAP: %a"
        Bap_main.Extension.Error.pp err

let loaded = ()
