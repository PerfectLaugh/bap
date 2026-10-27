#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let check name ok = if not ok then failwith name

let expect_error expected f =
  match f () with
  | _ -> failwith expected
  | exception Failure msg when String.is_substring msg ~substring:expected -> ()

let le32 value =
  let data = Stdlib.Bytes.create 4 in
  Stdlib.Bytes.set_int32_le data 0 value;
  Stdlib.Bytes.to_string data

let le64 value =
  let data = Stdlib.Bytes.create 8 in
  Stdlib.Bytes.set_int64_le data 0 value;
  Stdlib.Bytes.to_string data

let engine = function
  | "unicorn" -> `Unicorn
  | "lifted" -> `Lifted
  | name -> failwithf "unknown engine %s" name ()

let create file kind = Emu.create ~engine:(engine kind) (Bap_script.project file)

let pcs trace =
  let values = Emu.Trace.pcs ~last:8 trace in
  List.init (Bigarray.Array1.dim values) ~f:(Bigarray.Array1.get values)

let tids trace =
  let values = Emu.Trace.tids ~last:8 trace in
  List.init (Bigarray.Array1.dim values) ~f:(Bigarray.Array1.get values)

let sizes trace =
  let values = Emu.Trace.sizes ~last:8 trace in
  List.init (Bigarray.Array1.dim values) ~f:(Bigarray.Array1.get values)

let () =
  Bap_script.init ();
  match Bap_script.args () with
  | [ file; work; kind; blocks ] ->
      let blocks = Bool.of_string blocks in
      let emu = create file kind in
      let finish = Emu.symbols emu |> List.find_exn ~f:(fun (name, _) ->
          String.equal name "s_loop_ret") |> snd
      in
      let trace =
        Emu.Trace.start ~size:8 ~blocks ~accesses:16 ~read_values:true
          ~code_versions:8 emu
      in
      ignore (Emu.run emu ~until:finish);
      let original_pcs = pcs trace and original_tids = tids trace in
      let original_sizes = sizes trace and original_window = Emu.Trace.inspect trace in
      check "wrapped trace is empty" (List.length original_pcs > 0);
      let state_file = Filename.concat work (sprintf "wrap-%s-%b.trace" kind blocks) in
      Emu.Trace.save_state trace state_file;
      let restored = Emu.Trace.restore_state (create file kind) state_file in
      check "restored count differs"
        (Int64.equal (Emu.Trace.count trace) (Emu.Trace.count restored));
      check "restored PCs differ" (List.equal Int64.equal original_pcs (pcs restored));
      check "restored TIDs differ" (List.equal Int64.equal original_tids (tids restored));
      check "restored block sizes differ"
        (List.equal Int32.equal original_sizes (sizes restored));
      check "restored instruction window differs"
        (Poly.equal original_window (Emu.Trace.inspect restored));
      check "restored hot PCs are all zero"
        (List.exists (Emu.Trace.hot restored) ~f:(fun (pc, _) -> Int64.(pc <> 0L)));
      Emu.Trace.resume restored;
      Emu.Trace.resume restored;
      Emu.Trace.stop restored;
      let corrupt_file = state_file ^ ".corrupt" in
      let single = create file kind in
      let pc = Emu.pc single in
      let trace = Emu.Trace.start ~size:8 ~blocks ~code_versions:8 single in
      ignore (Emu.step single);
      let single_file = state_file ^ ".single" in
      Emu.Trace.save_state trace single_file;
      let corrupted =
        String.substr_replace_all (In_channel.read_all single_file)
          ~pattern:(le64 pc) ~with_:(String.make 8 '\000')
      in
      Out_channel.write_all corrupt_file ~data:corrupted;
      expect_error "only zero program counters" (fun () ->
          Emu.Trace.restore_state (create file kind) corrupt_file);
      if blocks then begin
        let size =
          match Bigarray.Array1.get (Emu.Trace.sizes trace) 0 with
          | size when Int32.(size > 0l) -> size
          | _ -> failwith "single block has zero size"
        in
        let corrupted =
          String.substr_replace_all (In_channel.read_all single_file)
            ~pattern:(le32 size) ~with_:(String.make 4 '\000')
        in
        Out_channel.write_all corrupt_file ~data:corrupted;
        expect_error "only zero block sizes" (fun () ->
            Emu.Trace.restore_state (create file kind) corrupt_file)
      end;
      print_endline "wrapped trace state restored"
  | _ -> failwith "expected PROGRAM WORK ENGINE BLOCKS"
