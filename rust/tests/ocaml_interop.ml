external ogre_parse : string -> (string, string) result = "ogre_rs_parse"
external ogre_merge : string -> string -> (string, string) result = "ogre_rs_merge"
external ogre_yaml : string -> (string, string) result = "ogre_rs_yaml"

let unwrap = function Ok value -> value | Error message -> failwith message
let expect expected actual = if expected <> actual then failwith (Printf.sprintf "expected %S, got %S" expected actual)

let () =
  let document = "(declare student (name str) (age int))\n(student \"Jane Doe\" 0x15)\n" in
  expect "(declare student (name str) (age int))\n(student \"Jane Doe\" 21)\n" (unwrap (ogre_parse document));
  expect (unwrap (ogre_parse document)) (unwrap (ogre_merge document ""));
  if String.length (unwrap (ogre_yaml document)) = 0 then failwith "yaml";
  print_endline "OCaml/Rust OGRE interoperability passed"
