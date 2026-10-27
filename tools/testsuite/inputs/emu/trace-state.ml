#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let midpoint = 0x40046dL
let finish = 0x400494L
let watched = (0x403008L, 0x40300bL)
let check name ok = if not ok then failwith name

type observation = {
  count : int64;
  retained : int;
  pcs : int64 list;
  window : (int64 * int64 * int64 option * int * bool) list;
  accesses : Emu.Trace.access list;
  branches : Emu.Trace.branch list;
  slice : Emu.slice;
  sampled_count : int64;
  sampled_pcs : int64 list;
  sampled_window : (int64 * int64 * int64 option * int * bool) list;
  watched_accesses : Emu.Trace.access list;
}

let engine = function
  | "unicorn" -> `Unicorn
  | "lifted" -> `Lifted
  | name -> failwithf "unknown engine %s" name ()

let create file kind =
  Emu.create ~engine:(engine kind) ~args:[ "a"; "b"; "c" ]
    (Bap_script.project file)

let pcs trace =
  let pcs = Emu.Trace.pcs trace in
  List.init (Bigarray.Array1.dim pcs) ~f:(Bigarray.Array1.get pcs)

let window trace =
  Emu.Trace.inspect trace
  |> List.map ~f:(fun (i : Emu.Trace.window_instruction) ->
      ( i.index,
        i.pc,
        i.block,
        i.thread,
        match i.decode with Decoded -> true | Decode_failed -> false ))

let start emu =
  ( Emu.Trace.start ~size:(1 lsl 16) ~accesses:(1 lsl 16) ~read_values:true emu,
    Emu.Trace.start ~size:1024 ~every:3 ~first:0x400470L ~last:finish emu,
    Emu.Trace.start ~size:1024 ~accesses:128 ~watch:watched emu )

let counts (main, sampled, watched) =
  (Emu.Trace.count main, Emu.Trace.count sampled, Emu.Trace.count watched)

let run_until emu addr =
  match Emu.run emu ~until:addr with
  | Paused -> ()
  | _ -> failwithf "the program did not pause at %Lx" addr ()

let observe (main, sampled, watched) =
  {
    count = Emu.Trace.count main;
    retained = Emu.Trace.retained main;
    pcs = pcs main;
    window = window main;
    accesses = Emu.Trace.accesses main;
    branches = Emu.Trace.branches main;
    slice = Emu.slice main [ Emu.Reg "RAX" ];
    sampled_count = Emu.Trace.count sampled;
    sampled_pcs = pcs sampled;
    sampled_window = window sampled;
    watched_accesses = Emu.Trace.accesses watched;
  }

let save path observation =
  Out_channel.write_all path
    ~data:(Marshal.to_string observation [ Marshal.No_sharing ])

let load path = (Marshal.from_string (In_channel.read_all path) 0 : observation)

let expect_error text f =
  match f () with
  | _ -> false
  | exception Failure msg -> String.is_substring msg ~substring:text
  | exception _ -> false

let reference file kind work =
  let emu = create file kind in
  let traces = start emu in
  run_until emu finish;
  save (Filename.concat work (kind ^ ".expected")) (observe traces)

let produce file kind work other_program other_target =
  let emu = create file kind in
  let traces = start emu in
  let main, sampled, watched = traces in
  let main_file = Filename.concat work (kind ^ ".main.trace") in
  let sampled_file = Filename.concat work (kind ^ ".sampled.trace") in
  let watched_file = Filename.concat work (kind ^ ".watched.trace") in
  run_until emu midpoint;
  let saved_count = Emu.Trace.count main in
  Emu.Trace.save_state main main_file;
  let first = In_channel.read_all main_file in
  Emu.Trace.save_state main main_file;
  check "atomic replacement changed an unchanged snapshot"
    (String.equal first (In_channel.read_all main_file));
  Emu.Trace.save_state sampled sampled_file;
  Emu.Trace.save_state watched watched_file;
  let restored = Emu.Trace.restore_state (create file kind) main_file in
  check "restored count differs"
    (Int64.equal (Emu.Trace.count restored) saved_count);
  Emu.Trace.stop restored;
  Emu.Trace.stop restored;
  let data = In_channel.read_all main_file in
  let magic = "bap-emu-trace-state 3\n" in
  let versioned = Filename.concat work (kind ^ ".version.trace") in
  Out_channel.write_all versioned
    ~data:
      ("bap-emu-trace-state 2\n"
      ^ String.sub data ~pos:(String.length magic)
          ~len:(String.length data - String.length magic));
  let truncated = Filename.concat work (kind ^ ".truncated.trace") in
  Out_channel.write_all truncated
    ~data:(String.prefix data (String.length data / 2));
  let invalid = Filename.concat work (kind ^ ".invalid.trace") in
  Out_channel.write_all invalid ~data:"not a trace state";
  check "unsupported version accepted"
    (expect_error "unsupported version" (fun () ->
         Emu.Trace.restore_state (create file kind) versioned));
  check "truncated snapshot accepted"
    (expect_error "broken" (fun () ->
         Emu.Trace.restore_state (create file kind) truncated));
  check "invalid format accepted"
    (expect_error "another format" (fun () ->
         Emu.Trace.restore_state (create file kind) invalid));
  check "snapshot from another program accepted"
    (expect_error "another program" (fun () ->
         Emu.Trace.restore_state (create other_program kind) main_file));
  check "snapshot from another target accepted"
    (expect_error "another target" (fun () ->
         Emu.Trace.restore_state
           (Emu.create ~engine:(engine kind) (Bap_script.project other_target))
           main_file));
  check "save error is not clear"
    (expect_error "save_state" (fun () ->
         Emu.Trace.save_state main (Filename.concat work "missing/state")));
  check "read error is not clear"
    (expect_error "restore_state" (fun () ->
         Emu.Trace.restore_state emu (Filename.concat work "missing/state")));
  printf "%s producer ok\n" kind

let consume file kind work =
  let emu = create file kind in
  let main =
    Emu.Trace.restore_state emu (Filename.concat work (kind ^ ".main.trace"))
  in
  let sampled =
    Emu.Trace.restore_state emu (Filename.concat work (kind ^ ".sampled.trace"))
  in
  let watched =
    Emu.Trace.restore_state emu (Filename.concat work (kind ^ ".watched.trace"))
  in
  let traces = (main, sampled, watched) in
  let before = counts traces in
  Emu.Trace.stop main;
  Emu.Trace.stop sampled;
  Emu.Trace.stop watched;
  run_until emu midpoint;
  check "detached traces recorded the replayed prefix"
    (Poly.equal (counts traces) before);
  List.iter [ main; sampled; watched ] ~f:(fun trace ->
      Emu.Trace.resume trace;
      Emu.Trace.resume trace);
  Emu.Trace.stop main;
  Emu.Trace.stop main;
  Emu.Trace.stop watched;
  Emu.Trace.resume main;
  Emu.Trace.resume main;
  Emu.Trace.resume watched;
  Emu.Trace.resume watched;
  run_until emu finish;
  let expected = load (Filename.concat work (kind ^ ".expected")) in
  let actual = observe traces in
  if not (Int64.equal expected.count actual.count) then
    failwithf "count differs: expected %Ld, got %Ld" expected.count actual.count
      ();
  check "retention differs" (expected.retained = actual.retained);
  check "pcs differ" (List.equal Int64.equal expected.pcs actual.pcs);
  check "global indices differ" (Poly.equal expected.window actual.window);
  check "accesses differ" (Poly.equal expected.accesses actual.accesses);
  check "branches differ" (Poly.equal expected.branches actual.branches);
  check "slices differ" (Poly.equal expected.slice actual.slice);
  check "sampling count differs"
    (Int64.equal expected.sampled_count actual.sampled_count);
  check "sampling pcs differ"
    (List.equal Int64.equal expected.sampled_pcs actual.sampled_pcs);
  check "sampling indices differ"
    (Poly.equal expected.sampled_window actual.sampled_window);
  check "watched accesses differ"
    (Poly.equal expected.watched_accesses actual.watched_accesses);
  check "sampled trace escaped its code range"
    (List.for_all actual.sampled_pcs ~f:(fun pc ->
         Int64.(pc >= 0x400470L && pc <= finish)));
  check "watched trace escaped its memory range"
    (List.for_all actual.watched_accesses ~f:(fun (a : Emu.Trace.access) ->
         Int64.(a.addr >= 0x403008L && a.addr <= 0x40300bL)));
  Out_channel.write_all
    (Filename.concat work (kind ^ ".consumer-ok"))
    ~data:"ok\n"

let () =
  match Bap_script.args () with
  | [ "reference"; file; kind; work; _; _ ] -> reference file kind work
  | [ "produce"; file; kind; work; other_program; other_target ] ->
      produce file kind work other_program other_target
  | [ "consume"; file; kind; work; _; _ ] -> consume file kind work
  | _ ->
      failwith
        "expected reference|produce|consume PROGRAM ENGINE WORK OTHER-PROGRAM \
         OTHER-TARGET"
