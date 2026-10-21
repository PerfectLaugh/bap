(* [bap script [--cache-dir=DIR] FILE.ml ARG...] compiles the script to a plugin of the
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

(* the directory is removed as much as possible, as Windows doesn't
   remove the plugin that bap has loaded, which stays in the temporary
   directory *)
let remove_dir dir =
  let ignore_errors f = try f () with Sys_error _ -> () in
  if Stdlib.Sys.file_exists dir then begin
    Stdlib.Sys.readdir dir
    |> Array.iter ~f:(fun f ->
        ignore_errors (fun () -> Stdlib.Sys.remove (Filename.concat dir f)));
    ignore_errors (fun () -> Stdlib.Sys.rmdir dir)
  end

(* the compiled scripts are cached by the digest of their source, their
   libraries, and the bap that runs them, whose libraries they are
   compiled with, which is told by the size and the time of its
   executable, and without the cache, i.e., the --cache-dir option, they
   are compiled into a temporary directory *)
let cache_dir = function
  | None ->
      let dir = Stdlib.Filename.temp_dir "bap-script-" "" in
      at_exit (fun () -> remove_dir dir);
      dir
  | Some cache ->
      let dir = Filename.concat cache "scripts" in
      let rec mkdir dir =
        if not (Stdlib.Sys.file_exists dir) then begin
          mkdir (Filename.dirname dir);
          try Stdlib.Sys.mkdir dir 0o755 with Sys_error _ -> ()
        end
      in
      mkdir dir;
      dir

let unit_name ~libs source =
  let bap = Caml_unix.LargeFile.stat Stdlib.Sys.executable_name in
  let key =
    String.concat ~sep:"\000"
      (sprintf "%Ld:%f" bap.st_size bap.st_mtime :: source :: libs)
  in
  (* the name is unique, as Dynlink loads a unit once *)
  "bap_script_" ^ Stdlib.Digest.(to_hex (string key))

(* the script is compiled in a directory of its own, and the plugin is
   moved to the cache, once it is complete *)
let compile ~cache ~unit ~libs source =
  let dir = Stdlib.Filename.temp_dir ~temp_dir:cache "build" "" in
  at_exit (fun () -> remove_dir dir);
  let ml = Filename.concat dir (unit ^ ".ml") in
  Out_channel.write_all ml ~data:source;
  let includes =
    output ~error:"can't find the libraries"
      (sprintf "ocamlfind query -r -i-format %s"
         (String.concat ~sep:" " (List.map ~f:Filename.quote libs)))
      (Filename.concat dir "includes")
    |> String.split_lines |> String.concat ~sep:" "
  in
  command ~error:"can't compile the script"
    (sprintf "ocamlopt -c %s %s" includes (Filename.quote ml));
  (* the plugin is linked without the includes, which the libraries,
     loaded by bap, don't need, as ocamlopt passes them to the linker,
     whose command they make longer than Windows allows *)
  let built = Filename.concat dir (unit ^ ".cmxs") in
  command ~error:"can't link the script"
    (sprintf "ocamlopt -shared -o %s %s" (Filename.quote built)
       (Filename.quote (Filename.concat dir (unit ^ ".cmx"))));
  let cmxs = Filename.concat cache (unit ^ ".cmxs") in
  Stdlib.Sys.rename built cmxs;
  cmxs

(* a cached script, which the libraries of a new bap don't fit, is
   compiled anew *)
let rec load ~recompile file cmxs =
  match Dynlink.loadfile cmxs with
  | () -> Stdlib.exit 0
  | exception Dynlink.Error (Library's_module_initializers_failed exn) ->
      fail "%s failed: %s" file (Exn.to_string exn)
  | exception Dynlink.Error err -> (
      match recompile with
      | Some compile ->
          Stdlib.Sys.remove cmxs;
          load ~recompile:None file (compile ())
      | None -> fail "%s" (Dynlink.error_message err))

let run ?cache file args =
  let source =
    try In_channel.read_all file with Sys_error msg -> fail "%s" msg
  in
  let required, source = requires source in
  let source = sprintf "# 1 %S\n%s" file source in
  let libs = "bap-frontend.script" :: required in
  let cache = cache_dir cache in
  let unit = unit_name ~libs source in
  let compile () = compile ~cache ~unit ~libs source in
  let cached = Filename.concat cache (unit ^ ".cmxs") in
  let cmxs, recompile =
    if Stdlib.Sys.file_exists cached then (cached, Some compile)
    else (compile (), None)
  in
  Bap_script.set_args args;
  (* the libraries are loaded, as the plugins are, so that the plugins,
     which bap loads later, don't load them again *)
  List.iter required ~f:(fun lib ->
      try Dune_site_plugins.V1.load lib
      with exn -> fail "can't load %s: %s" lib (Exn.to_string exn));
  load ~recompile file cmxs

let usage = "usage: bap script [--cache-dir=DIR] FILE.ml [ARG]..."

let rec main ?cache = function
  | "--cache-dir" :: dir :: args -> main ~cache:dir args
  | opt :: args when String.is_prefix opt ~prefix:"--cache-dir=" ->
      main ~cache:(String.chop_prefix_exn opt ~prefix:"--cache-dir=") args
  | ("-h" | "--help") :: _ ->
      print_endline usage;
      Stdlib.exit 0
  | file :: args -> run ?cache file args
  | [] -> fail "%s" usage
