open Core
open OUnit2
open Bap_plugins.Std

let suite =
  "MIPS"
  >::: [
         Test_mips32eb.suite;
         Test_mips32le.suite;
         Test_mips64eb.suite;
         Test_mips64le.suite;
         Test_mips64eb_64.suite;
         Test_mips64le_64.suite;
       ]

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () -> run_test_tt_main suite
