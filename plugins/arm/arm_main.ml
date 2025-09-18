let doc =
  "\n\
   # DESCRIPTION\n\n\
   The target support package that enables support for the ARM family of\n\
   architectures.\n"

open Core
open Bap.Std
open Bap_main
open Extension.Syntax

include struct
  open Extension

  let interworking =
    Configuration.parameter
      Type.(some bool)
      "interworking"
      ~doc:
        "Enable ARM/Thumb interworking. Defaults to (auto),\n\
        \            i.e., to the automatic detection of interworking"

  let backend =
    Configuration.parameter
      Type.(some string)
      "backend"
      ~doc:
        "Specify the backend that is used for disassembly and\n\
        \            lifting."

  let features =
    Configuration.parameters
      Type.(list string)
      "features"
      ~doc:
        "Additional target features/attributes. The syntax\n\
        \            and the feature names are backend-specific. For the LLVM\n\
        \            backend the features are passed to the target attributes,\n\
        \            see $(b,llvm-mc -mattr=help -triple <target>) for the list\n\
        \            of features supported by your version of LLVM. To enable a\n\
        \            feature just pass its name (you can optionally prepend\n\
        \            $(b,+) to its name), to disable a feature prepend $(b,-)\n\
        \            to its name."
end

type arms = [ Arch.arm | Arch.armeb | Arch.thumb | Arch.thumbeb ]
[@@deriving enumerate]

let () =
  Bap_main.Extension.declare ~doc @@ fun ctxt ->
  let interworking = ctxt --> interworking in
  let backend = ctxt --> backend in
  let features = List.concat (ctxt --> features) in
  Arm_target.load ~features ?backend ?interworking ();
  Arm_gnueabi.setup ();
  List.iter all_of_arms ~f:(fun arch ->
      register_target (arch :> arch) (module ARM));
  Ok ()
