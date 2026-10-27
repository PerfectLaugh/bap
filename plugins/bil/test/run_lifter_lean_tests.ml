open Core
open OUnit2
open Bap_plugins.Std
open Bap.Std
open Result.Monad_infix
module Proof = Bap_bil_plugin.Bil_lifter_proof

let mode target encoding = Lifter_test.mode ~addr:0x20000 ~target ~encoding ()
let a64 = mode "armv8-a+le" "llvm-aarch64"
let a32 = mode "armv7-a+fp+le" "llvm-armv7"
let mips32 = mode "mipsel" "llvm-mips32le"
let mips64 = mode "mips64el" "llvm-mips64le"
let ppc32 = mode "powerpc" "llvm-powerpc32"
let ppc64 = mode "powerpc64le" "llvm-powerpc64le"
let riscv32 = mode "riscv32" "llvm-riscv32"
let riscv64 = mode "riscv64" "llvm-riscv64"
let operations = [ Proof.Add; Proof.Sub; Proof.And; Proof.Or; Proof.Xor ]

let operation_name = function
  | Proof.Add -> "ADD"
  | Proof.Sub -> "SUB"
  | Proof.And -> "AND"
  | Proof.Or -> "OR"
  | Proof.Xor -> "XOR"

let arm_regs = ("R0", "R1", "R2")
let mips_regs = ("R3", "R1", "R2")
let riscv_regs = ("X1", "X2", "X3")

let cases =
  [
    ( "AArch64",
      a64,
      64,
      arm_regs,
      [
        "20 00 02 8b";
        "20 00 02 cb";
        "20 00 02 8a";
        "20 00 02 aa";
        "20 00 02 ca";
      ] );
    ( "AArch64-32",
      a64,
      32,
      arm_regs,
      [
        "20 00 02 0b";
        "20 00 02 4b";
        "20 00 02 0a";
        "20 00 02 2a";
        "20 00 02 4a";
      ] );
    ( "ARM32",
      a32,
      32,
      arm_regs,
      [
        "02 00 81 e0";
        "02 00 41 e0";
        "02 00 01 e0";
        "02 00 81 e1";
        "02 00 21 e0";
      ] );
    ( "MIPS32",
      mips32,
      32,
      mips_regs,
      [
        "21 18 22 00";
        "23 18 22 00";
        "24 18 22 00";
        "25 18 22 00";
        "26 18 22 00";
      ] );
    ( "MIPS64",
      mips64,
      64,
      mips_regs,
      [
        "2d 18 22 00";
        "2f 18 22 00";
        "24 18 22 00";
        "25 18 22 00";
        "26 18 22 00";
      ] );
    ( "PowerPC32",
      ppc32,
      32,
      arm_regs,
      [
        "7c 01 12 14";
        "7c 01 10 50";
        "7c 01 10 38";
        "7c 01 13 78";
        "7c 01 12 78";
      ] );
    ( "PowerPC64",
      ppc64,
      64,
      arm_regs,
      [
        "14 12 01 7c";
        "50 10 01 7c";
        "38 10 01 7c";
        "78 13 01 7c";
        "78 12 01 7c";
      ] );
    ( "RISCV32",
      riscv32,
      32,
      riscv_regs,
      [
        "b3 00 31 00";
        "b3 00 31 40";
        "b3 70 31 00";
        "b3 60 31 00";
        "b3 40 31 00";
      ] );
    ( "RISCV64",
      riscv64,
      64,
      riscv_regs,
      [
        "b3 00 31 00";
        "b3 00 31 40";
        "b3 70 31 00";
        "b3 60 31 00";
        "b3 40 31 00";
      ] );
  ]

let validate_mba bil destination =
  Proof.execute bil >>= fun state ->
  Proof.output state destination >>= fun actual ->
  match Type.infer actual with
  | Error error -> Error (Type.sexp_of_error error |> Sexp.to_string_hum)
  | Ok (Type.Mem _ | Type.Unk) -> Error "the lifted result is not an immediate"
  | Ok (Type.Imm width) ->
      let before = Bil.BinOp (Bil.PLUS, actual, Bil.int (Word.zero width)) in
      Bap_recompile.simplify_exp_checked before
      |> Result.map_error ~f:Error.to_string_hum
      >>| fun _ -> ()

let validate ~operation ~width ~destination ~left ~right mode code =
  let bil = Lifter_test.lift mode code in
  Proof.validate_reg_reg ~operation ~width ~destination ~left ~right bil
  |> Result.map_error ~f:(fun message ->
      Format.asprintf "%s@.Lifted BIL:@.%a" message Bil.pp bil)
  >>= fun () -> validate_mba bil destination

let assert_ok = function Ok () -> () | Error message -> assert_failure message

let architecture_tests =
  List.concat_map cases ~f:(fun (architecture, mode, width, regs, codes) ->
      let destination, left, right = regs in
      List.map2_exn operations codes ~f:(fun operation code ->
          let destination, left, right =
            if
              String.equal architecture "PowerPC32"
              || String.equal architecture "PowerPC64"
            then
              match operation with
              | Proof.Sub -> (destination, right, left)
              | Proof.And | Proof.Or | Proof.Xor -> ("R1", "R0", "R2")
              | Proof.Add -> (destination, left, right)
            else (destination, left, right)
          in
          sprintf "%s-%s" architecture (operation_name operation) >:: fun _ ->
          assert_ok
            (validate ~operation ~width ~destination ~left ~right mode code)))

let negative_tests =
  [
    ( "wrong operation" >:: fun _ ->
      match
        validate ~operation:Proof.Sub ~width:64 ~destination:"R0" ~left:"R1"
          ~right:"R2" a64 "20 00 02 8b"
      with
      | Ok () -> assert_failure "Lean accepted the wrong operation"
      | Error _ -> () );
    ( "wrong width" >:: fun _ ->
      match
        validate ~operation:Proof.Add ~width:64 ~destination:"R0" ~left:"R1"
          ~right:"R2" a64 "20 00 02 0b"
      with
      | Ok () -> assert_failure "Lean accepted the wrong width"
      | Error _ -> () );
    ( "unexpected writes" >:: fun _ ->
      match
        validate ~operation:Proof.Add ~width:64 ~destination:"R0" ~left:"R1"
          ~right:"R2" a64 "20 00 02 ab"
      with
      | Ok () -> assert_failure "flag-setting ADD was accepted as plain ADD"
      | Error _ -> () );
    ( "unsupported statement" >:: fun _ ->
      match
        Proof.validate_reg_reg ~operation:Proof.Add ~width:64 ~destination:"R0"
          ~left:"R1" ~right:"R2" [ Bil.Special "trap" ]
      with
      | Ok () -> assert_failure "a special statement was accepted"
      | Error _ -> () );
  ]

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () ->
      run_test_tt_main
        ("multi_architecture_lifter_lean"
        >::: architecture_tests @ negative_tests)
