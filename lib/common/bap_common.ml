open Bap_common_private_sites.Sites

let ( / ) = Filename.concat

(* dune tells the program the locations of the sites and of the
   libraries in the environment, when it runs the program, otherwise
   the program, that is run from the build tree, e.g., as
   _build/default/src/bap_frontend.exe, uses the install tree of its
   context and the libraries, that it was built with *)
let install =
  match Sys.getenv_opt "DUNE_DIR_LOCATIONS" with
  | Some _ -> None
  | None ->
      let rec build dir =
        let parent = Filename.dirname dir in
        if String.equal parent dir then None
        else if String.equal (Filename.basename dir) "_build" then Some dir
        else build parent
      in
      Option.bind
        (build (Filename.dirname Sys.executable_name))
        (fun dir ->
          let install = dir / "install" / Bap_common_build.context in
          if Sys.file_exists install then Some install else None)

let () =
  Option.iter
    (fun install ->
      let sep = if Sys.win32 then ";" else ":" in
      let path paths =
        String.concat sep (List.filter (fun p -> p <> "") paths)
      in
      let env var = Option.value (Sys.getenv_opt var) ~default:"" in
      let stdlib = Bap_common_build.stdlib in
      Unix.putenv "OCAMLPATH"
        (path [ install / "lib"; env "OCAMLPATH"; Bap_common_build.ocamlpath ]);
      if Sys.getenv_opt "DUNE_OCAML_STDLIB" = None then
        Unix.putenv "DUNE_OCAML_STDLIB" stdlib;
      if Sys.getenv_opt "DUNE_OCAML_HARDCODED" = None then
        Unix.putenv "DUNE_OCAML_HARDCODED"
          (path [ stdlib; Filename.dirname stdlib ]))
    install

let located section suffix = function
  | [] -> (
      match install with
      | Some install -> [ install / section / "bap-common" / suffix ]
      | None -> [])
  | dirs -> dirs

let share = located "share"

module Plugins = Dune_site_plugins.Private_.Plugins.Make (struct
  let paths = located "lib" "plugins" plugins
end)

let sites = function
  | "api" -> share "api" api
  | "ghidra" -> share "ghidra" ghidra
  | "lisp" -> share "lisp" lisp
  | "plugins" -> Plugins.paths
  | "primus" -> share "primus" primus
  | "semantics" -> share "semantics" semantics
  | "signatures" -> share "signatures" signatures
  | "site-lisp" | "site_lisp" -> share "site_lisp" site_lisp
  | unknown -> failwith ("Invalid site: " ^ unknown)
