#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let addr emu name =
  List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name

let run emu until =
  match Emu.run emu ~until with
  | Paused -> ()
  | _ -> failwithf "the program doesn't pause at %Lx" until ()

let reason = function
  | Some Emu.No_dataflow -> "none"
  | Some Unresolved_inputs -> "inputs"
  | Some Outside_trace_writes -> "outside"
  | Some Instruction_decode -> "decode"
  | None -> "steps"

let decoded (i : Emu.Trace.window_instruction) =
  match i.decode with Decoded -> true | Decode_failed -> false

let scrubbed prog blocks =
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project prog) in
  let entry = addr emu "main" and stop = addr emu "print_endline" in
  let trace = Emu.Trace.start ~blocks ~accesses:128 emu in
  run emu entry;
  let first = Emu.Trace.count trace in
  run emu stop;
  let last = Emu.Trace.count trace in
  let window = Int64.(to_int_exn (last - first)) in
  Emu.Trace.inspect ~executed_bytes:true ~last:window trace
  |> List.filter_map ~f:(fun (i : Emu.Trace.window_instruction) ->
      Option.map (Emu.insn_at emu i.pc) ~f:(fun insn -> (i.pc, insn.bytes)))
  |> List.iter ~f:(fun (pc, bytes) ->
      Emu.write emu pc (String.make (String.length bytes) '\xff'));
  let inspected = Emu.Trace.inspect ~last:window trace in
  let s = Emu.slice ~window trace [ Emu.Reg "R10" ] in
  let recovered_window =
    Emu.Trace.inspect ~executed_bytes:true ~last:window trace
  in
  let recovered =
    Emu.slice ~executed_bytes:true ~window trace [ Emu.Reg "R0" ]
  in
  let metadata =
    (not (List.is_empty inspected))
    && List.for_all inspected ~f:(fun i ->
        Int64.(i.index >= first && i.index < last) && i.thread >= 0)
  in
  let attribution =
    List.for_all s.decode_failures ~f:(fun f ->
        if blocks then
          Option.exists f.block ~f:(fun block -> Int64.(f.pc >= block))
        else Option.is_none f.block)
  in
  let explicit =
    List.is_empty s.steps
    && Option.equal Poly.equal s.reason (Some Emu.Instruction_decode)
    && (not (List.is_empty s.decode_failures))
    && List.exists inspected ~f:(Fn.non decoded)
    && attribution
  in
  let recovered =
    (not (List.is_empty recovered.steps))
    && Option.is_none recovered.reason
    && List.is_empty recovered.decode_failures
    && (not (List.is_empty recovered_window))
    && List.for_all recovered_window ~f:decoded
  in
  printf "scrubbed %s: metadata %b, explicit %b, recovered %b\n"
    (if blocks then "blocks" else "instructions")
    metadata explicit recovered

let reasons prog =
  let emu = Emu.create (Bap_script.project prog) in
  let entry = addr emu "s_zero" and stop = addr emu "s_zero_ret" in
  let trace = Emu.Trace.start ~accesses:128 emu in
  run emu entry;
  let first = Emu.Trace.count trace in
  run emu stop;
  let window = Int64.(to_int_exn (Emu.Trace.count trace - first)) in
  let none = Emu.slice ~window trace [] in
  let inputs = Emu.slice ~window trace [ Emu.Reg "R10" ] in
  printf "empty reasons: %s %s, complete %b\n" (reason none.reason)
    (reason inputs.reason) none.complete

let native_gap prog blocks =
  let emu = Emu.create (Bap_script.project prog) in
  let entry = addr emu "s_hooked" and stop = addr emu "s_hooked_ret" in
  let at = addr emu "s_hooked_at" in
  Emu.on_code ~first:at ~last:at emu (fun emu _ -> Emu.set_reg emu "R10" 42L);
  let trace = Emu.Trace.start ~blocks ~accesses:128 emu in
  run emu entry;
  let first = Emu.Trace.count trace in
  run emu stop;
  let window = Int64.(to_int_exn (Emu.Trace.count trace - first)) in
  let s = Emu.slice ~window trace [ Emu.Reg "R10" ] in
  List.is_empty s.steps
  && Option.equal Poly.equal s.reason (Some Emu.Outside_trace_writes)
  && not (List.is_empty s.gaps)

let () =
  match Bap_script.args () with
  | [ aarch64; x86 ] ->
      List.iter [ false; true ] ~f:(scrubbed aarch64);
      reasons x86;
      printf "native gap: instructions %b, blocks %b\n" (native_gap x86 false)
        (native_gap x86 true)
  | _ -> failwith "expected AARCH64-ECHO X86-SLICE-WEIRD"
