open Ocamlbuild_plugin
open Bap_build.Std

(* On Windows, the built plugins are copied into the directory of the
   sources, not linked, see Bap_build, so the copies of the previous
   builds are removed, as otherwise ocamlbuild would take them for the
   sources of the targets, and wouldn't rebuild them. *)
let remove_copied_plugins () =
  if Sys.win32 then
    Array.iteri
      (fun i arg ->
        if
          i > 0
          && Filename.check_suffix arg ".plugin"
          && Sys.file_exists arg
          && Sys.file_exists (Filename.concat "_build" arg)
        then Sys.remove arg)
      Sys.argv

let main () =
  remove_copied_plugins ();
  Plugin_options.set ();
  Ocamlbuild_plugin.dispatch (function
    | Before_rules -> Plugin_rules.install ()
    | _ -> ());
  Ocamlbuild_unix_plugin.setup ();
  Ocamlbuild_pack.Main.main ()

let () = main ()
