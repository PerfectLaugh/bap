open Core
open Bap_main
open Bap_primus.Std

let package = "bap"

let () =
  Extension.declare ~doc:"runs the binary programs in Primus with Unicorn"
    ~provides:[ "primus"; "unicorn" ]
  @@ fun _ ->
  Primus.Components.register_generic ~package "load-binary-unicorn"
    (module Bap_primus_unicorn_plugin.Primus_unicorn_executor.Loader)
    ~desc:
      "Links the binary program, like load-binary, so that its subroutines run \
       in the Unicorn CPU emulator, except those that other components \
       replace, e.g., with Lisp stubs.";
  let component = Primus.System.component ~package in
  (* bap:binary-executor with load-binary-unicorn instead of load-binary *)
  Primus.System.Repository.add
  @@ Primus.System.define ~package "unicorn-binary-executor"
       ~desc:"Executes a binary program in Unicorn."
       ~components:
         (List.map ~f:component
            [
              "load-binary-unicorn";
              "program-loader";
              "x86-registers-initializer";
              "x86-setup-plt";
              "powerpc-init";
              "observation-printer";
            ]);
  Primus.System.Repository.add
  @@ Primus.System.define ~package "unicorn-executor"
       ~desc:
         "Executes a binary in Unicorn together with the Lisp Machine, which \
          runs the stubs."
       ~depends_on:
         [
           Primus.System.depends_on ~package "unicorn-binary-executor";
           Primus.System.depends_on ~package "base-lisp-machine";
         ];
  Ok ()
