open Bap_plugins.Std

(* the printer is the name of a function, e.g., Bap.Std.Word.pp, the
   printers whose names aren't visible in the toplevel, e.g., those of
   modules whose interfaces aren't in its path, are skipped *)
let install_printer printer =
  let quiet = Format.make_formatter (fun _ _ _ -> ()) ignore in
  match Longident.unflatten (String.split_on_char '.' printer) with
  | None -> ()
  | Some name -> ( try Topdirs.dir_install_printer quiet name with _ -> ())

let install_printers () = List.iter install_printer (Core.Pretty_printer.all ())

(* The plugins that are packages are loaded with topfind, which knows the
   libraries that are already loaded, e.g., bap.top and its dependencies,
   unlike dune-site, which loads them again, so the plugins would extend
   another instance of Bap_main, which the toplevel rebinds to, than the
   one that initializes them. The packages of a plugin are the requires
   of its META file, which dune generates in the plugins site. *)
let plugin_packages name =
  let meta =
    List.find_map
      (fun dir ->
        let meta = Filename.concat (Filename.concat dir name) "META" in
        if Sys.file_exists meta then Some meta else None)
      (Bap_common.sites "plugins")
  in
  match meta with
  | None -> failwith ("the plugin " ^ name ^ " is not found")
  | Some meta ->
      In_channel.with_open_text meta In_channel.input_all
      |> String.split_on_char '\n'
      |> List.concat_map (fun line ->
          let line = String.trim line in
          match (String.index_opt line '"', String.rindex_opt line '"') with
          | Some i, Some j when j > i && String.starts_with ~prefix:"requires" line
            ->
              String.sub line (i + 1) (j - i - 1)
              |> String.map (function ',' -> ' ' | c -> c)
              |> String.split_on_char ' '
              |> List.filter (fun s -> s <> "")
          | _ -> [])

let load_plugin name = Topfind.load_deeply (plugin_packages name)

let main () =
  let module Bap_std_is_required = Bap.Std in
  let module Core_is_required = Core in
  let loader = Topdirs.dir_load Format.err_formatter in
  setup_dynamic_loader loader;
  setup_package_loader load_plugin;
  match Bap_main.init ~argv:[| "baptop" |] () with
  | Ok () ->
      install_printers ();
      ()
  | Error failed ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp failed;
      exit 1

let () = main ()
