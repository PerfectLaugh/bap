open Bap_plugins.Std

let install_printer printer =
  Topdirs.dir_install_printer Format.err_formatter
    (Option.get @@ Longident.unflatten printer)

let install_printers () = Core.Pretty_printer.all () |> install_printer

let main () =
  let module Bap_std_is_required = Bap.Std in
  let module Core_is_required = Core in
  let loader = Topdirs.dir_load Format.err_formatter in
  setup_dynamic_loader loader;
  match Bap_main.init ~argv:[| "baptop" |] () with
  | Ok () ->
      install_printers ();
      ()
  | Error failed ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp failed;
      exit 1

let () = main ()
