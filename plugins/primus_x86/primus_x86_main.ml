open Bap.Std
open Bap_primus.Std
include Self ()

let init _ =
  Primus.System.Repository.update ~package:"bap" "legacy-main" ~f:(fun s ->
      Primus.System.add_component s ~package:"bap" "x86-registers-initializer");
  Primus.Components.register_generic ~package:"bap" "x86-registers-initializer"
    (module Primus_x86_loader.InitializeRegisters)
    ~desc:"Intializes all x86/x86-64 registers to zero.";

  Primus.System.Repository.update ~package:"bap" "legacy-main" ~f:(fun s ->
      Primus.System.add_component s ~package:"bap" "x86-setup-plt");
  Primus.Components.register_generic ~package:"bap" "x86-setup-plt"
    (module Primus_x86_loader.SetupPLT)
    ~desc:"Sets up PLT entries."
;;

Config.manpage
  [
    `S "DESCRIPTION";
    `P
      "Performs the x86 target specific setup. So far it just initializes\n\
      \  all flag registers to zero.";
  ]
;;

Config.declare_extension ~doc:"x86 Primus Support package"
  ~provides:[ "abi"; "x86"; "primus" ] init
