open OUnit2

let suite =
  "ARM"
  >::: [
         Test_a64.suite;
         Test_a64fp.suite;
         Test_a32.suite;
         Test_a32_qemu.suite;
         Test_vfp.suite;
         Test_t32.suite;
         Test_t32_branches.suite;
         Test_t32_qemu.suite;
       ]

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () -> run_test_tt_main suite
