open Bap.Std
include Self ()

let () =
  Config.manpage
    [
      `S "DESCRIPTION";
      `P
        "Provides the PowerPC targets, decoders and ABI. The semantics of the \
         instructions is in the Primus Lisp files of the powerpc package.";
    ]

let backend = Config.param Config.(some string) "backend"

let () =
  Config.declare_extension ~doc:"provides the PowerPC targets"
    ~provides:[ "semantics"; "lifter"; "powerpc" ] (fun { get } ->
      Bap_powerpc_target.load ?backend:(get backend) ();
      Powerpc_abi.setup ())
