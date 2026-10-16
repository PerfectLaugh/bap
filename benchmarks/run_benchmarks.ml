open Core
open Core_bench

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@."
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () ->
      Command_unix.run @@ Bench.make_command
      @@ List.concat [ Bench_dom.tests (); Bench_image.tests ]
