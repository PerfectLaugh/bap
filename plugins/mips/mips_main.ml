open Core
open Bap.Std
open Bap_core_theory
include Self ()

let () =
  Config.manpage
    [
      `S "DESCRIPTION";
      `P
        "Provides the MIPS targets, decoders and ABI. The semantics of the \
         instructions is in the Primus Lisp files of the mips package.";
    ]

(* the branches and jumps that are followed by a delay slot *)
let delayed =
  Set.of_list
    (module String)
    [
      "BEQ";
      "BNE";
      "BGEZ";
      "BGTZ";
      "BLEZ";
      "BLTZ";
      "BGEZAL";
      "BLTZAL";
      "BEQL";
      "BNEL";
      "BGEZL";
      "BGTZL";
      "BLEZL";
      "BLTZL";
      "BGEZALL";
      "BLTZALL";
      "J";
      "JAL";
      "JR";
      "JALR";
      "JR_HB";
      "JALR_HB";
      "BEQ64";
      "BNE64";
      "BGEZ64";
      "BGTZ64";
      "BLEZ64";
      "BLTZ64";
      "JR64";
      "JALR64";
      "BC1T";
      "BC1F";
      "BC1TL";
      "BC1FL";
      (* the release 6, whose compact branches have no delay slots *)
      "BAL";
      "NAL";
      "BC1EQZ";
      "BC1NEZ";
      "JALR_HB64";
      "JR_HB_R6";
      "JR_HB64_R6";
      "JALR64_R6";
    ]

let promise_delay_slots () =
  KB.Rule.(
    declare ~package:"mips" "delay-slot"
    |> require Insn.Slot.name |> provide Insn.Slot.delay
    |> comment "provides the delay slot length for branches");
  KB.promise Theory.Semantics.slot @@ fun obj ->
  let open KB.Syntax in
  Theory.Label.target obj >>= fun target ->
  KB.guard (Theory.Target.belongs Bap_mips_target.parent target) >>= fun () ->
  KB.collect Theory.Semantics.slot obj >>| fun insn ->
  let name = KB.Value.get Insn.Slot.name insn in
  if Set.mem delayed name then KB.Value.put Insn.Slot.delay insn (Some 1)
  else Insn.empty

let backend =
  Config.param
    Config.(some string)
    "backend" ~doc:"Specify which backend to use"

let () =
  Config.declare_extension ~doc:"provides MIPS semantics"
    ~provides:[ "semantics"; "lifter"; "mips" ] (fun { get } ->
      Bap_mips_target.load ?backend:(get backend) ();
      promise_delay_slots ();
      Mips_abi.setup ())
