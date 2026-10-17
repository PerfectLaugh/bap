open Core
open Bap_core_theory
open Bap.Std
open KB.Syntax
module Dis = Disasm_expert.Basic

type mode = A64 | A32 | T32

let addr = 0x10000
let bits = function A64 -> 64 | A32 | T32 -> 32

let target mode =
  Theory.Target.get ~package:"bap"
    (match mode with A64 -> "armv8-a+le" | A32 | T32 -> "armv7-a+fp+le")

let encoding mode =
  Theory.Language.read ~package:"bap"
    (match mode with
    | A64 -> "llvm-aarch64"
    | A32 -> "llvm-armv7"
    | T32 -> "llvm-thumb")

let bytes_of_hex code =
  String.split code ~on:' '
  |> List.filter ~f:(Fn.non String.is_empty)
  |> List.map ~f:(fun b -> Char.of_int_exn (Int.of_string ("0x" ^ b)))
  |> String.of_char_list

let new_insn mode mem insn =
  KB.Object.create Theory.Program.cls >>= fun code ->
  (* one unit for each target, as the target of a unit is fixed *)
  let name = match mode with A64 -> "a64" | A32 | T32 -> "a32" in
  KB.Symbol.intern name Theory.Unit.cls >>= fun unit ->
  KB.provide Theory.Unit.target unit (target mode) >>= fun () ->
  KB.provide Theory.Label.encoding code (encoding mode) >>= fun () ->
  KB.provide Theory.Label.addr code (Some (Bitvec.M64.int addr)) >>= fun () ->
  KB.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) @@ fun () ->
  KB.provide Memory.slot code (Some mem) >>= fun () ->
  KB.provide Dis.Insn.slot code (Some insn) >>= fun () ->
  KB.collect Theory.Semantics.slot code >>| fun _ -> code

let lift mode code =
  let data = Bigstring.of_string (bytes_of_hex code) in
  let base = Addr.of_int ~width:(bits mode) addr in
  let mem = Or_error.ok_exn (Memory.create LittleEndian base data) in
  let dis = Or_error.ok_exn (Dis.lookup (target mode) (encoding mode)) in
  let insn =
    match Dis.insn_of_mem dis mem with
    | Ok (_, Some insn, _) -> insn
    | Ok (_, None, _) -> failwithf "%s: not an instruction" code ()
    | Error err -> failwithf "%s: %s" code (Error.to_string_hum err) ()
  in
  match Toplevel.try_eval Theory.Semantics.slot (new_insn mode mem insn) with
  | Error conflict ->
      failwithf "%s: the lifters failed: %s" code
        (Format.asprintf "%a" KB.Conflict.pp conflict)
        ()
  | Ok sema -> Insn.bil sema

(* the type of a register, flag or memory by its name *)
let typ mode name =
  let is prefix = String.is_prefix name ~prefix in
  match (mode, name) with
  | _, ("NF" | "ZF" | "CF" | "VF" | "QF") -> Type.imm 1
  | A64, _ when is "V" -> Type.imm 128
  | A64, _ -> Type.imm 64
  | (A32 | T32), _ when is "D" -> Type.imm 64
  | (A32 | T32), _ -> Type.imm 32

let mem mode =
  let size = match mode with A64 -> `r64 | A32 | T32 -> `r32 in
  Var.create "mem" (Type.mem size `r8)

let word width value = Word.create (Bitvec.of_string value) width

type location =
  | Reg of var
  | Mem of int * int  (** the number of bytes and the address *)
  | Pc

let location mode name =
  match String.lsplit2 name ~on:'@' with
  | Some (n, a) when String.is_prefix n ~prefix:"M" ->
      Mem (Int.of_string (String.drop_prefix n 1), Int.of_string a)
  | _ when String.equal name "PC" -> Pc
  | _ -> Reg (Var.create name (typ mode name))

let size_of_bytes n = Size.of_int_exn (8 * n)

(* the statement that stores [value] in the location [name] *)
let initialize mode (name, value) =
  match location mode name with
  | Reg v ->
      let width = match Var.typ v with Type.Imm w -> w | _ -> assert false in
      Bil.(v := int (word width value))
  | Mem (n, a) ->
      let mem = mem mode in
      let addr = Word.of_int ~width:(bits mode) a in
      let value = word (8 * n) value in
      Bil.(
        mem :=
          store ~mem:(var mem) ~addr:(int addr) (int value) LittleEndian
            (size_of_bytes n))
  | Pc -> failwith "PC can't be initialized"

let check_typed asm bil =
  match Type.check bil with
  | Ok () -> ()
  | Error err ->
      OUnit2.assert_failure
        (sprintf "%s: the lifted code is not well-typed: %s" asm
           (Type.Error.to_string err))

let case mode asm code ~init ~expect =
  OUnit2.( >:: ) asm @@ fun _ctxt ->
  let bil = List.map init ~f:(initialize mode) @ lift mode code in
  check_typed asm bil;
  (* the expected memory words are loaded into fresh variables *)
  let loads, expect =
    List.fold_map expect ~init:[] ~f:(fun loads (name, value) ->
        match location mode name with
        | Mem (n, a) ->
            let v = Var.create ~fresh:true "word" (Type.imm (8 * n)) in
            let mem = mem mode in
            let addr = Word.of_int ~width:(bits mode) a in
            let load =
              Bil.(
                v :=
                  load ~mem:(var mem) ~addr:(int addr) LittleEndian
                    (size_of_bytes n))
            in
            (load :: loads, (name, Reg v, value))
        | loc -> (loads, (name, loc, value)))
  in
  let state = Primus_bil.eval ~target:(target mode) (bil @ List.rev loads) in
  List.iter expect ~f:(fun (name, loc, value) ->
      let got, width =
        match loc with
        | Reg v ->
            let width =
              match Var.typ v with Type.Imm w -> w | _ -> assert false
            in
            (Primus_bil.lookup state v, width)
        | Pc -> (Primus_bil.pc state, bits mode)
        | Mem _ -> assert false
      in
      let expected = word width value in
      match got with
      | Some got when Word.equal got expected -> ()
      | got ->
          OUnit2.assert_failure
            (sprintf "%s: %s is %s, expected %s" asm name
               (Option.value_map got ~default:"not set" ~f:Word.to_string)
               (Word.to_string expected)))
