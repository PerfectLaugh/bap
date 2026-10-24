#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The slices of the result, RAX or R0, at the returns of the odd cases
   of slice-weird.c, or of arm-slice-weird.c, with [arm], over their
   windows, from their entries, by the instructions and by the blocks,
   as the steps in the case, by its labels and offsets, the repeated ones
   counted, and the locations, that are live at its entry, i.e., its
   inputs, and the gaps, by the labels of their records. *)

let sym emu name =
  List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name

let describe syms pc =
  match
    List.filter syms ~f:(fun (_, a) -> Int64.(a <= pc))
    |> List.max_elt ~compare:(fun (_, a) (_, b) -> Int64.compare a b)
  with
  | Some (n, a) when Int64.(pc - a < 0x1000L) ->
      if Int64.(pc = a) then n else sprintf "%s+%Ld" n Int64.(pc - a)
  | _ -> sprintf "%Lx" pc

let compress names =
  List.group names ~break:String.( <> )
  |> List.map ~f:(function
    | [ n ] -> n
    | n :: _ as l -> sprintf "%s*%d" n (List.length l)
    | [] -> "")

let location = function Emu.Reg r -> r | Mem (_, n) -> sprintf "mem:%d" n
let result = ref "RAX"

let show ?(tag = "") ?last ?(accesses = 4096) ?(early = fun _ -> ())
    ?(setup = fun _ -> ()) prog name blocks =
  let emu = Emu.create ~args:[ "a"; "b" ] (Bap_script.project prog) in
  let syms =
    List.filter (Emu.symbols emu) ~f:(fun (n, _) ->
        List.exists [ "s_"; "a_"; "t_" ] ~f:(fun prefix ->
            String.is_prefix n ~prefix)
        || List.mem [ "fact"; "copied" ] n ~equal:String.equal)
  in
  early emu;
  let trace = Emu.Trace.start ~blocks ~accesses emu in
  let run until =
    match Emu.run emu ~until with
    | Paused -> ()
    | _ -> failwithf "%s doesn't pause at %Lx" name until ()
  in
  run (sym emu name);
  let entry = Emu.Trace.count trace in
  setup emu;
  run (sym emu (name ^ "_ret"));
  let count = Emu.Trace.count trace in
  let window =
    match last with Some n -> n | None -> Int64.(to_int_exn (count - entry))
  in
  let s = Emu.slice ~window trace [ Emu.Reg !result ] in
  let pcs = Emu.Trace.pcs trace in
  let at r =
    let i = Bigarray.Array1.dim pcs - Int64.(to_int_exn (count - r)) in
    describe syms (Bigarray.Array1.get pcs i)
  in
  printf "%s%s %s: %s | live %s | gaps %s | complete %b\n%!" name tag
    (if blocks then "b" else "i")
    (List.map s.steps ~f:(fun st -> describe syms st.Emu.pc)
    |> compress |> String.concat ~sep:" ")
    (List.map s.live ~f:location |> String.concat ~sep:",")
    (List.map s.gaps ~f:at |> String.concat ~sep:",")
    s.complete

let both ?tag ?last ?accesses ?early ?setup prog name =
  show ?tag ?last ?accesses ?early ?setup prog name false;
  show ?tag ?last ?accesses ?early ?setup prog name true

let cases =
  [
    "s_zero";
    "s_partial";
    "s_kill32";
    "s_bytes";
    "s_bytekill";
    "s_overlap";
    "s_cmov_no";
    "s_cmov_yes";
    "s_xchg";
    "s_rep";
    "s_pushf";
    "s_callpop";
    "s_sse";
    "s_div";
    "s_setcc";
    "s_pushmem";
    "s_loop";
    "s_cmpxchg";
    "s_cmpxchg_fail";
    "s_smc";
    "s_fact";
    "s_copied";
  ]

let arm =
  [
    "a_cond_no";
    "a_cond_yes";
    "a_ldm";
    "a_pool";
    "a_shift";
    "a_umull";
    "a_bytes";
    "a_strex";
    "a_link";
    "a_carry";
    "t_ite";
    "a_interwork";
    "t_loop";
    "t_pool";
    "a_vfp";
    "a_ldrd";
    "a_frame";
    "a_ldrne";
    "a_wback";
    "a_mrs";
    "t_frame";
    "a_copied";
  ]

let () =
  match Bap_script.args () with
  | [ prog; "arm" ] ->
      result := "R0";
      List.iter arm ~f:(both prog);
      let hook emu =
        let at = sym emu "a_hooked_at" in
        Emu.on_code ~first:at ~last:at emu (fun emu _ ->
            Emu.set_reg emu "R0" 1000L)
      in
      both ~setup:hook prog "a_hooked"
  | [ prog ] ->
      List.iter cases ~f:(both prog);
      (* the hook writes RAX, before or after the trace starts *)
      let hook emu =
        let at = sym emu "s_hooked_at" in
        Emu.on_code ~first:at ~last:at emu (fun emu _ ->
            Emu.set_reg emu "RAX" 1000L)
      in
      both ~tag:"/after" ~setup:hook prog "s_hooked";
      both ~tag:"/before" ~early:hook prog "s_hooked";
      (* the script writes the slot, that the case stored *)
      let write emu =
        (match Emu.run emu ~until:(sym emu "s_written_at") with
        | Paused -> ()
        | _ -> failwith "s_written doesn't pause");
        Emu.write emu (Emu.reg emu "RSP") "\x07\x00\x00\x00\x00\x00\x00\x00"
      in
      both ~setup:write prog "s_written";
      (* the rings of the accesses lose the first iterations *)
      both ~tag:"/4" ~accesses:4 prog "s_rep";
      both ~tag:"/12" ~accesses:12 prog "s_rep";
      (* the window ends at the last iteration, which copies nothing *)
      both ~tag:"/last3" ~last:3 prog "s_rep"
  | _ -> failwith "expected the program"
