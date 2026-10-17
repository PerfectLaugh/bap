open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open KB.Syntax
include Self ()

(* the common ABIs (ms, gnu, cdecl, ...) are declared by the Core
   Theory in the [core] package, while the x86-specific ones (pascal,
   thiscall, ...) are declared in the [bap] package, so we look up
   unqualified names in both. *)
let read_abi name =
  try Theory.Abi.read ~package:"core" name
  with Invalid_argument _ -> Theory.Abi.read ~package:"bap" name

(* (x86-prefix BYTE) is true if BYTE is a legacy prefix of the
   instruction, e.g., 0xf3 (REP), as LLVM doesn't keep them in the
   opcodes of the string instructions *)
let declare_prefix_primitive () =
  let types = Primus.Lisp.Type.Spec.(one int @-> bool) in
  Primus.Lisp.Semantics.declare ~types ~package:"x86-common" "x86-prefix"
    ~docs:
      "(x86-prefix BYTE) is true if BYTE, e.g., 0xf3, is a legacy prefix of \
       the instruction" ~body:(fun _ ->
      Theory.instance () >>= Theory.require >>= fun (module CT) ->
      KB.return @@ fun lbl args ->
      let* mem = KB.collect Memory.slot lbl in
      let byte =
        match args with
        | [ x ] -> KB.Value.get Primus.Lisp.Semantics.static x
        | _ -> None
      in
      let present =
        match (mem, byte) with
        | Some mem, Some byte ->
            X86_prefix.get mem
            |> List.exists ~f:(fun p ->
                X86_prefix.to_int p = Bitvec.to_int byte)
        | _ -> false
      in
      let* r = if present then CT.b1 else CT.b0 in
      let r =
        KB.Value.put Primus.Lisp.Semantics.static r
          (Some (if present then Bitvec.one else Bitvec.zero))
      in
      let+ eff = CT.perform Theory.Effect.Sort.bot in
      KB.Value.put Theory.Semantics.value eff (Theory.Value.forget r))

let () =
  Config.manpage
    [
      `S "SYNOPSIS";
      `P "$(b,bap) FILE [--x86-abi=ABI]";
      `P "$(b,bap) FILE [--x86-64-abi=ABI]";
      `S "DESCRIPTION";
      `P
        "Provides the x86 and x86-64 targets, decoders and ABIs. The semantics \
         of the instructions is in the Primus Lisp files of the x86 packages. \
         No parameters are usually required, though it is possible to override \
         the detected ABI, e.g., when working with an executable compiled for \
         the MS Windows platform. For a full set of supported ABI use the \
         corresponding list option.";
      `S "EXAMPLE";
      `P
        "To choose a correct ABI for a binary compiled for MS Windows x64 \
         target, use the following:";
      `P "$(b,bap) FILE --x86-64-abi=ms";
      `S "SEE ALSO";
      `P "$(b,bap-x86-cpu)(3), $(b,bap-plugin-abi)(1), $(b,bap-plugin-arm)(1)";
    ]

let abi =
  let doc = "Override the ABI detection and use the selected ABI." in
  Config.(param (some string) "abi" ~synonyms:[ "64-abi" ] ~doc)

let fp_lifter = Config.flag "with-floating-points" ~doc:"DEPRECATED"

let legacy_lifter =
  Config.flag "with-legacy-floating-points"
    ~doc:"DEPRECATED, the legacy floating-point lifter was removed"

let disable_intrinsics =
  Config.flag "disable-floating-point-intrinsics"
    ~doc:
      "Disables translation of floating-point instructions into calls to \
       intrinsic functions."

let cet_enabled =
  Config.flag "cet-enabled" ~synonyms:[ "endbr-enabled" ]
    ~doc:
      "When enabled, translate all endbr instruction into intrinsic calls. \
       Otherwise treat them as nops"

let backend =
  Config.param Config.(some string) "backend" ~synonyms:[ "64-backend" ]

(* the lifters were merged, the option is kept so that the scripts that
   select one still work *)
let lifter : [ `legacy | `modern | `merge ] Config.param =
  let kinds = [ ("legacy", `legacy); ("modern", `modern); ("merge", `merge) ] in
  Config.(
    param (enum kinds) "lifter" ~default:`merge
      ~doc:"DEPRECATED, the semantics is in the Primus Lisp files only")

let () =
  Config.declare_extension ~doc:"provides x86/x86-64 semantics"
    ~provides:[ "disassembler"; "lifter"; "semantics"; "x86"; "abi" ]
  @@ fun { Config.get = ( !! ) } ->
  X86_target.load ?abi:(Option.map ~f:read_abi !!abi) ?backend:!!backend ();
  if !!fp_lifter || !!legacy_lifter then
    warning
      "the legacy x87 floating-point lifter was removed, the \
       --x86-with-floating-points and --x86-with-legacy-floating-points \
       options are ignored";
  if Poly.equal !!lifter `legacy then
    warning
      "the legacy x86 lifter was removed, the --x86-lifter option is ignored";
  declare_prefix_primitive ();
  let features =
    (if !!disable_intrinsics then []
     else [ ("x86-floating-points", [ "intrinsic-semantics" ]) ])
    @ if !!cet_enabled then [ ("x86-cet", [ "enabled" ]) ] else []
  in
  KB.promise Primus.Lisp.Semantics.context @@ fun _ ->
  KB.return @@ Primus.Lisp.Context.create features
