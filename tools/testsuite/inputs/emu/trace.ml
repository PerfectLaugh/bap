#require "bap-primus-unicorn.emu"

open Core
module Emu = Bap_emu

let last a = Bigarray.Array1.(get a (dim a - 1))

(* the instructions of the trace of the blocks are those of the trace of
   each instruction, and the native trace saves them *)
let trace crc file =
  let run blocks =
    let emu = Emu.create (Bap_script.project crc) in
    let trace = Emu.Trace.start ~size:(1 lsl 20) ~blocks emu in
    ignore (Emu.run emu);
    (Emu.Trace.count trace, Emu.Trace.insns ~last:(1 lsl 17) trace, trace)
  in
  let count, insns, trace = run false in
  let blocks, block_insns, _ = run true in
  printf "instructions %Ld, blocks %Ld\n" count blocks;
  let n = Bigarray.Array1.dim insns and m = Bigarray.Array1.dim block_insns in
  let same =
    List.for_all (List.range 1 (Int.min n m + 1)) ~f:(fun i ->
        Int64.equal
          (Bigarray.Array1.get insns (n - i))
          (Bigarray.Array1.get block_insns (m - i)))
  in
  printf "the last instructions are the same: %b, the last is %Lx\n" same
    (last insns);
  let saved = Emu.Trace.save ~last:1000 trace file in
  let lines = In_channel.read_lines file in
  printf "saved %Ld, %d lines, the last is %s\n" saved (List.length lines)
    (List.last_exn lines)

(* the slice of the result at the return of main, through the stack, by
   the instructions, or by the blocks, has the gap at main, whose
   arguments the stub of __libc_start_main passes *)
let slice prog blocks =
  let emu = Emu.create ~args:[ "a"; "b"; "c" ] (Bap_script.project prog) in
  let trace = Emu.Trace.start ~blocks ~accesses:4096 emu in
  ignore (Emu.run emu ~until:0x400494L);
  let s = Emu.slice trace [ Emu.Reg "RAX" ] in
  let main = List.find s.steps ~f:(fun s -> Int64.(s.pc >= 0x400446L)) in
  let before =
    List.filter s.steps ~f:(fun s -> Int64.(s.pc < 0x400446L))
    |> List.last
    |> Option.value_map ~default:(-1L) ~f:(fun s -> s.Emu.index)
  in
  printf "slice of %s: %s\n"
    (if blocks then "blocks" else "instructions")
    (List.filter_map s.steps ~f:(fun s ->
         Option.some_if Int64.(s.pc >= 0x400446L) (sprintf "%Lx" s.pc))
    |> String.concat ~sep:" ");
  printf "gap at main: %b, complete: %b\n"
    (match main with
    | Some { index; _ } ->
        List.exists s.gaps ~f:(fun gap -> Int64.(before < gap && gap <= index))
    | None -> false)
    s.complete

let () =
  match Bap_script.args () with
  | [ crc; prog; file ] ->
      trace crc file;
      slice prog false;
      slice prog true
  | _ -> failwith "expected CRC SLICE FILE"
