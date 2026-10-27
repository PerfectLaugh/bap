#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let check name ok = if not ok then failwith name

let engine = function
  | "unicorn" -> `Unicorn
  | "lifted" -> `Lifted
  | name -> failwithf "unknown engine %s" name ()

let create prog kind =
  Emu.create ~engine:(engine kind) ~args:[ "a"; "b" ] (Bap_script.project prog)

let sym emu name =
  List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name

let run emu until =
  match Emu.run emu ~until with
  | Paused -> ()
  | _ -> failwithf "the program did not pause at %Lx" until ()

let expect_failure text f =
  match f () with
  | _ -> false
  | exception Failure msg -> String.is_substring msg ~substring:text
  | exception _ -> false

let produce prog kind blocks prefix =
  let emu = create prog kind in
  let entry = sym emu "s_smc" and finish = sym emu "s_smc_ret" in
  run emu entry;
  let trace =
    Emu.Trace.start ~size:8 ~accesses:64 ~blocks ~code_versions:8
      ~journal:prefix ~journal_interval:8 emu
  in
  for _ = 1 to 4 do
    run emu finish;
    Emu.set_pc emu entry
  done;
  run emu finish;
  let first_count = Emu.Trace.count trace in
  Emu.Trace.stop trace;
  Emu.set_pc emu entry;
  Emu.Trace.resume trace;
  Emu.Trace.resume trace;
  run emu finish;
  Emu.Trace.stop trace;
  Emu.Trace.stop trace;
  check "too few records for the small rings"
    Int64.(Emu.Trace.count trace > first_count && first_count > 8L);
  check "native ring is not bounded" (Emu.Trace.retained trace <= 16);
  check "version ring is not bounded"
    (Emu.Trace.retained_versions trace > 0
    && Emu.Trace.retained_versions trace <= 8);
  let segments = Emu.Trace.journal_segments prefix in
  check "rotation and resume did not produce enough segments"
    (List.length segments >= 4);
  check "manifest end does not match the producer"
    (Int64.equal (List.last_exn segments).next (Emu.Trace.count trace));
  List.iteri segments ~f:(fun i segment ->
      check "manifest sequence is not deterministic" (segment.sequence = i);
      check "segment filename is not deterministic"
        (String.equal
           (Filename.basename segment.file)
           (sprintf "%s.%08d.trace" (Filename.basename prefix) i)));
  let loaded = Emu.Trace.load_journal emu prefix in
  check "manifest loading lost segments"
    (List.length loaded = List.length segments);
  List.iter2_exn loaded segments ~f:(fun trace segment ->
      check "consumer count is discontinuous"
        (Int64.equal (Emu.Trace.count trace) segment.next);
      check "consumer native ring is not bounded"
        (Emu.Trace.retained trace <= 16);
      check "consumer version ring is not bounded"
        (Emu.Trace.retained_versions trace <= 8));
  segments

let deterministic prog kind blocks work =
  let base = sprintf "%s/%s-%b" work kind blocks in
  let left = produce prog kind blocks (base ^ "-left") in
  let right = produce prog kind blocks (base ^ "-right") in
  check "deterministic runs produced different segment counts"
    (List.length left = List.length right);
  List.iter2_exn left right ~f:(fun left right ->
      check "segment sequence differs" (left.sequence = right.sequence);
      check "segment boundaries differ"
        (Int64.equal left.first right.first && Int64.equal left.next right.next);
      check "segment bytes differ"
        (String.equal
           (In_channel.read_all left.file)
           (In_channel.read_all right.file)))

let recorded_at trace site =
  Emu.Trace.versions trace
  |> List.find_map ~f:(fun (v : Emu.Trace.code_version) ->
      if v.block then
        if Int64.(site >= v.pc && site - v.pc < of_int (String.length v.bytes))
        then
          let offset = Int64.(to_int_exn (site - v.pc)) in
          if String.length v.bytes - offset >= 3 then
            Some (String.sub v.bytes ~pos:offset ~len:3)
          else None
        else None
      else if Int64.equal site v.pc && String.length v.bytes >= 3 then
        Some (String.prefix v.bytes 3)
      else None)

let decoded_at window site =
  List.exists window ~f:(fun (i : Emu.Trace.window_instruction) ->
      Int64.equal i.pc site
      && match i.decode with Decoded -> true | Decode_failed -> false)

let self_modifying prog kind blocks work =
  let emu = create prog kind in
  let entry = sym emu "s_smc" and finish = sym emu "s_smc_ret" in
  let site = Int64.(entry + 2L) in
  run emu entry;
  let prefix = sprintf "%s/%s-%b-smc" work kind blocks in
  let trace =
    Emu.Trace.start ~size:32 ~accesses:64 ~blocks ~code_versions:64
      ~journal:prefix ~journal_interval:8 emu
  in
  run emu finish;
  Emu.Trace.stop trace;
  check "self-modifying case did not patch current bytes"
    (String.equal (Emu.read emu Int64.(site + 2L) 1) "\xf1");
  let original = Option.value_exn (recorded_at trace site) in
  check "wrong instruction bytes were captured"
    (String.equal original "\x48\x89\xf9");
  let expected_window = Emu.Trace.inspect ~executed_bytes:true trace in
  check "live inspect did not use the recorded instruction"
    (decoded_at expected_window site);
  let expected_slice = Emu.slice ~executed_bytes:true trace [ Emu.Reg "RAX" ] in
  check "self-modifying slice is empty"
    (not (List.is_empty expected_slice.steps));
  let state = sprintf "%s/%s-%b-smc.state" work kind blocks in
  Emu.Trace.save_state trace state;
  let fresh = create prog kind in
  Emu.write fresh Int64.(site + 2L) "\xff";
  check "fresh current bytes do not differ"
    (String.equal (Emu.read fresh Int64.(site + 2L) 1) "\xff");
  let restored = Emu.Trace.restore_state fresh state in
  check "detached restore lost code versions"
    (Option.equal String.equal (recorded_at restored site) (Some original));
  let restored_window = Emu.Trace.inspect ~executed_bytes:true restored in
  check "restored inspect did not use recorded bytes"
    (decoded_at restored_window site);
  let restored_slice =
    Emu.slice ~executed_bytes:true restored [ Emu.Reg "RAX" ]
  in
  check "restored slice differs" (Poly.equal expected_slice restored_slice);
  ignore (Emu.Trace.branches ~executed_bytes:true restored);
  ignore (Emu.Trace.calls ~executed_bytes:true restored)

let sampled prog kind work =
  let emu = create prog kind in
  let entry = sym emu "s_loop" and finish = sym emu "s_loop_ret" in
  run emu entry;
  let prefix = sprintf "%s/%s-sampled" work kind in
  let trace =
    Emu.Trace.start ~size:16 ~every:3 ~code_versions:8 ~journal:prefix
      ~journal_interval:3 emu
  in
  for iteration = 1 to 2 do
    run emu finish;
    Emu.Trace.stop trace;
    if iteration = 1 then begin
      Emu.set_pc emu entry;
      Emu.Trace.resume trace
    end
  done;
  let pcs = Emu.Trace.pcs trace in
  let first =
    Int64.(Emu.Trace.count trace - of_int (Bigarray.Array1.dim pcs))
  in
  let versions = Emu.Trace.versions ~last:(-1) trace in
  check "sampled version ring is empty or unbounded"
    ((not (List.is_empty versions)) && List.length versions <= 8);
  List.iter versions ~f:(fun (v : Emu.Trace.code_version) ->
      check "sampled version escaped native record indices"
        Int64.(v.index >= first && v.index < Emu.Trace.count trace);
      let native_pc =
        Bigarray.Array1.get pcs Int64.(to_int_exn (v.index - first))
      in
      check "a skipped instruction replaced a sampled version"
        (Int64.equal native_pc v.pc && not v.block));
  let last = List.last_exn versions in
  check "sampled resume lost its final record version"
    (Int64.equal last.index Int64.(Emu.Trace.count trace - 1L))

let overflow prog kind blocks work =
  let emu = create prog kind in
  let entry = sym emu "s_loop" and finish = sym emu "s_loop_ret" in
  run emu entry;
  let prefix = sprintf "%s/%s-%b-overflow" work kind blocks in
  let trace =
    Emu.Trace.start ~size:8 ~accesses:64 ~blocks ~code_versions:4
      ~journal:prefix ~journal_interval:1000 emu
  in
  ignore (Emu.run emu ~until:finish);
  check "code-version overflow was silent"
    (expect_failure "code-version overflow" (fun () -> Emu.Trace.stop trace));
  check "failed stop became silent on repetition"
    (expect_failure "code-version overflow" (fun () -> Emu.Trace.stop trace))

let io_errors prog kind blocks work =
  let emu = create prog kind in
  let missing = Filename.concat work "missing/journal" in
  check "journal creation I/O error is unclear"
    (expect_failure "Trace.start" (fun () ->
         Emu.Trace.start ~journal:missing emu));
  let entry = sym emu "s_zero" in
  run emu entry;
  let prefix = sprintf "%s/%s-%b-io" work kind blocks in
  let trace = Emu.Trace.start ~journal:prefix emu in
  ignore (Emu.step emu);
  Caml_unix.mkdir (prefix ^ ".00000000.trace") 0o755;
  check "stop did not surface segment I/O failure"
    (expect_failure "save_state" (fun () -> Emu.Trace.stop trace))

let () =
  match Bap_script.args () with
  | [ prog; kind; blocks; work ] ->
      let blocks = Bool.of_string blocks in
      deterministic prog kind blocks work;
      self_modifying prog kind blocks work;
      if not blocks then sampled prog kind work;
      overflow prog kind blocks work;
      io_errors prog kind blocks work;
      printf "%s blocks %b: journal ok\n" kind blocks
  | _ -> failwith "expected PROGRAM ENGINE BLOCKS WORK"
