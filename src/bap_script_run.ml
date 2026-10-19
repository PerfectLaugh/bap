(* [bap script FILE.ml ARG...] compiles the script to a plugin of the
   native code with the compiler of bap, which is the ocamlopt of the
   environment, as in opam or in dune exec, loads the libraries that it
   requires, and then the script, which starts bap, see Bap_script. *)

open Core

let fail fmt =
  Format.kasprintf
    (fun msg ->
      Format.eprintf "bap script: %s@." msg;
      Stdlib.exit 1)
    fmt

(* the libraries of the lines [#require "LIB,..."], which are blanked,
   so that the lines of the errors are of the script *)
let requires source =
  let libs = ref [] in
  let lines =
    String.split_lines source
    |> List.map ~f:(fun line ->
        match String.chop_prefix (String.strip line) ~prefix:"#require" with
        | None -> line
        | Some rest ->
            let names =
              String.strip rest
              |> String.strip ~drop:(Char.equal '"')
              |> String.split_on_chars ~on:[ ','; ' ' ]
              |> List.filter ~f:(Fn.non String.is_empty)
            in
            libs := !libs @ names;
            "")
  in
  (!libs, String.concat ~sep:"\n" lines ^ "\n")

let command ~error cmd =
  match Stdlib.Sys.command cmd with 0 -> () | _ -> fail "%s" error

let output ~error cmd file =
  command ~error (sprintf "%s > %s" cmd (Filename.quote file));
  In_channel.read_all file

let compile ~dir ~libs file source =
  let digest = Stdlib.Digest.(to_hex (string source)) in
  (* the name of the unit, which is unique, as Dynlink loads a unit once *)
  let unit = "bap_script_" ^ digest in
  let ml = Filename.concat dir (unit ^ ".ml") in
  Out_channel.write_all ml ~data:(sprintf "# 1 %S\n%s" file source);
  let includes =
    output ~error:"can't find the libraries"
      (sprintf "ocamlfind query -r -i-format %s"
         (String.concat ~sep:" " (List.map ~f:Filename.quote libs)))
      (Filename.concat dir "includes")
    |> String.split_lines |> String.concat ~sep:" "
  in
  let cmxs = Filename.concat dir (unit ^ ".cmxs") in
  command ~error:("can't compile " ^ file)
    (sprintf "ocamlopt -shared %s -o %s %s" includes (Filename.quote cmxs)
       (Filename.quote ml));
  cmxs

let run file args =
  let source =
    try In_channel.read_all file with Sys_error msg -> fail "%s" msg
  in
  let required, source = requires source in
  let dir = Filename_unix.temp_dir "bap-script" "" in
  (* the files of the script, which are loaded, are removed at the exit *)
  at_exit (fun () ->
      Stdlib.Sys.readdir dir
      |> Array.iter ~f:(fun f -> Stdlib.Sys.remove (Filename.concat dir f));
      Stdlib.Sys.rmdir dir);
  let cmxs =
    compile ~dir ~libs:("bap-frontend.script" :: required) file source
  in
  Bap_script.set_args args;
  (* the libraries are loaded, as the plugins are, so that the plugins,
     which bap loads later, don't load them again *)
  List.iter required ~f:(fun lib ->
      try Dune_site_plugins.V1.load lib
      with exn -> fail "can't load %s: %s" lib (Exn.to_string exn));
  let loaded = Result.try_with (fun () -> Dynlink.loadfile cmxs) in
  match Result.ok_exn loaded with
  | () -> Stdlib.exit 0
  | exception Dynlink.Error (Library's_module_initializers_failed exn) ->
      fail "%s failed: %s" file (Exn.to_string exn)
  | exception Dynlink.Error err -> fail "%s" (Dynlink.error_message err)
