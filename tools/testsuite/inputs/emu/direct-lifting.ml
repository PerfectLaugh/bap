#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

let check name ok = if not ok then failwith name

let bir_without_tids blks =
  List.concat_map blks ~f:(fun blk ->
      let defs =
        Term.enum def_t blk |> Seq.to_list
        |> List.map ~f:(fun def ->
               Printf.sprintf "%s := %s"
                 (Var.name (Def.lhs def))
                 (Exp.to_string (Def.rhs def)))
      in
      let jmps =
        Term.enum jmp_t blk |> Seq.to_list
        |> List.map ~f:(fun jmp ->
               match String.lsplit2 (Jmp.to_string jmp) ~on:' ' with
               | Some (_, text) -> text
               | None -> Jmp.to_string jmp)
      in
      defs @ jmps)

let () =
  Bap_script.init ();
  match Bap_script.args () with
  | [ file ] ->
      let run lifting =
        let emu =
          Emu.create ~engine:`Lifted ~lifting ~args:[ "hi" ]
            (Bap_script.project file)
        in
        let entry = Emu.pc emu in
        ignore (Emu.step emu);
        let size, entry_bir =
          match Emu.bir ~executed_bytes:true emu entry with
          | None -> failwith "entry has no BIR"
          | Some (size, blks) -> (size, bir_without_tids blks)
        in
        let entry_bytes = Emu.read emu entry size in
        Emu.write emu entry (String.make size '\001');
        let changed =
          match Emu.bir emu entry with
          | None -> []
          | Some (_, blks) -> bir_without_tids blks
        in
        check "changed bytes reused stale BIR"
          (not (List.equal String.equal entry_bir changed));
        Emu.write emu entry entry_bytes;
        let restored =
          match Emu.bir emu entry with
          | None -> failwith "restored entry has no BIR"
          | Some (_, blks) -> bir_without_tids blks
        in
        check "restored bytes did not restore BIR"
          (List.equal String.equal entry_bir restored);
        let trace =
          Emu.Trace.start ~size:(1 lsl 16) ~blocks:false ~accesses:4096
            ~read_values:true emu
        in
        let status = Emu.run emu in
        (status, entry_bir, Emu.Trace.insns trace, Emu.Trace.accesses trace)
      in
      let status, bir, insns, accesses = run `Default in
      let status', bir', insns', accesses' = run `Direct in
      let show_status = function
        | Emu.Paused -> "paused" | Emu.Running -> "running"
        | Emu.Exited code -> Option.value_map code ~default:"exited" ~f:Int.to_string
        | Emu.Failed msg -> "failed: " ^ msg
      in
      Printf.printf "default=%s direct=%s bir=%B insns=%B counts=%d/%d\n%!"
        (show_status status) (show_status status')
        (List.equal String.equal bir bir') (Poly.equal insns insns')
        (Bigarray.Array1.dim insns) (Bigarray.Array1.dim insns');
      check "exit status differs" (Poly.equal status status');
      if not (List.equal String.equal bir bir') then begin
        List.iter bir ~f:(Printf.printf "default BIR:\n%s\n%!");
        List.iter bir' ~f:(Printf.printf "direct BIR:\n%s\n%!")
      end;
      check "entry BIR differs" (List.equal String.equal bir bir');
      if not (Poly.equal insns insns') then begin
        let rec difference i =
          if i >= Bigarray.Array1.dim insns || i >= Bigarray.Array1.dim insns'
          then i
          else if Int64.equal insns.{i} insns'.{i} then difference (i + 1)
          else i
        in
        let i = difference 0 in
        let at trace i =
          if i < Bigarray.Array1.dim trace then Printf.sprintf "%Lx" trace.{i}
          else "end"
        in
        Printf.printf "first trace difference at %d: %s vs %s\n%!" i
          (at insns i) (at insns' i);
        List.iter
          (List.range (Int.max 0 (i - 4)) (i + 1))
          ~f:(fun j ->
            Printf.printf "trace %d: %s vs %s\n%!" j (at insns j) (at insns' j))
      end;
      check "instruction trace differs" (Poly.equal insns insns');
      let key (a : Emu.Trace.access) =
        (a.pc, a.addr, a.size, a.write, a.value, a.read_value)
      in
      check "memory trace differs"
        (Poly.equal (List.map accesses ~f:key) (List.map accesses' ~f:key));
      print_endline "direct lifting agrees with default lifting"
  | _ -> failwith "expected PROGRAM"
