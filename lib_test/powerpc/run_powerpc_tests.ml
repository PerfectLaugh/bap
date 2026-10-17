open OUnit2

let suite =
  "PowerPC"
  >::: [
         Test_ppc32.suite;
         Test_ppc64eb.suite;
         Test_ppc64le.suite;
         Test_ppc64eb_64.suite;
         Test_ppc64le_64.suite;
       ]

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () -> run_test_tt_main suite
