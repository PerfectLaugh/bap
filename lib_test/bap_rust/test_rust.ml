open Core
open OUnit2

let unwrap = function Ok value -> value | Error message -> failwith message

let test_ogre _ =
  let input = "(declare student (name str) (age int))\n(student \"Jane Doe\" 0x15)\n" in
  let normalized = Bap_rust.Ogre.normalize input |> unwrap in
  assert_bool "normalized" (String.is_substring normalized ~substring:"21");
  assert_equal normalized (Bap_rust.Ogre.merge input "" |> unwrap);
  assert_bool "yaml" (String.is_substring (Bap_rust.Ogre.yaml input |> unwrap) ~substring:"scheme:");
  assert_bool "json" (String.is_substring (Bap_rust.Ogre.json input |> unwrap) ~substring:"student");
  match Bap_rust.Ogre.normalize "(unknown)" with
  | Error _ -> ()
  | Ok _ -> assert_failure "expected an error"

let suite = "Rust OGRE" >::: [ "ogre" >:: test_ogre ]
let () = run_test_tt_main suite
