open Core
open Bap_main

type Extension.Error.t += Rust_error of string

let inputs = Extension.Command.arguments Extension.Type.string
let fail message = Error (Rust_error message)
let unwrap = function Ok value -> Ok value | Error message -> fail message
let ( let* ) value f = Result.bind value ~f

let rust_ogre mode files =
  let read file =
    try Ok (In_channel.read_all file) with Sys_error message -> fail message
  in
  match (mode, files) with
  | "merge", [ left; right ] ->
      let* left = read left in
      let* right = read right in
      let* output = Bap_rust.Ogre.merge left right |> unwrap in
      print_string output;
      Ok ()
  | ("normalize" | "yaml" | "json"), [ file ] ->
      let* input = read file in
      let convert =
        match mode with
        | "normalize" -> Bap_rust.Ogre.normalize
        | "yaml" -> Bap_rust.Ogre.yaml
        | _ -> Bap_rust.Ogre.json
      in
      let* output = convert input |> unwrap in
      print_endline output;
      Ok ()
  | _ ->
      fail
        "usage: rust-ogre normalize|yaml|json FILE or rust-ogre merge LEFT \
         RIGHT"

let () =
  Extension.Command.(
    declare ~doc:"process documents with Rust OGRE" "rust-ogre" (args $ inputs))
  @@ fun arguments _ctxt ->
  match arguments with
  | mode :: files -> rust_ogre mode files
  | [] ->
      fail
        "usage: rust-ogre normalize|yaml|json FILE or rust-ogre merge LEFT \
         RIGHT"
