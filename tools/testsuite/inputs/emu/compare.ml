#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu
module Compare = Emu.Compare

let instruction pc = Compare.Instruction { pc; thread = 1 }
let block pc = Compare.Block { pc; size = 4; thread = 1 }

let branch site =
  Compare.Branch { site; target = Int64.(site + 8L); taken = true; thread = 1 }

let call site =
  Compare.Call { site; targets = [ (Int64.(site + 16L), 2) ]; thread = 1 }

let capture site = Compare.Capture { site; values = [ 10L; 20L ]; thread = 1 }

let write pc =
  Compare.Write { pc; addr = 0x5000L; size = 8; value = 42L; thread = 1 }

let reason = function
  | Compare.Equal -> failwith "expected a difference"
  | Compare.Difference { reason; _ } -> reason

let event_differences =
  [
    ( instruction 0x1000L,
      instruction 0x1004L,
      function
      | Compare.Address_mismatch { field = Compare.Pc; _ } -> true
      | _ -> false );
    ( block 0x1000L,
      Compare.Block { pc = 0x1000L; size = 8; thread = 1 },
      function Compare.Size_mismatch _ -> true | _ -> false );
    ( branch 0x1000L,
      Compare.Branch
        { site = 0x1000L; target = 0x1008L; taken = false; thread = 1 },
      function Compare.Taken_mismatch _ -> true | _ -> false );
    ( call 0x1000L,
      Compare.Call { site = 0x1000L; targets = [ (0x1020L, 2) ]; thread = 1 },
      function
      | Compare.Address_mismatch { field = Compare.Target; _ } -> true
      | _ -> false );
    ( Compare.syscall ~thread:1 1L [ 10L; 20L ],
      Compare.syscall ~thread:1 1L [ 10L; 21L ],
      function
      | Compare.Values_mismatch { field = Compare.Arguments; position = 1; _ }
        ->
          true
      | _ -> false );
    ( capture 0x1000L,
      Compare.Capture { site = 0x1000L; values = [ 10L; 21L ]; thread = 1 },
      function
      | Compare.Values_mismatch { field = Compare.Registers; position = 1; _ }
        ->
          true
      | _ -> false );
    ( write 0x1000L,
      Compare.Write
        { pc = 0x1000L; addr = 0x5008L; size = 8; value = 42L; thread = 1 },
      function
      | Compare.Memory_address_mismatch
          { criterion = Compare.Mem (0x5000L, 8); _ } ->
          true
      | _ -> false );
    ( write 0x1000L,
      Compare.Write
        { pc = 0x1000L; addr = 0x5000L; size = 4; value = 42L; thread = 1 },
      function
      | Compare.Memory_size_mismatch { criterion = Compare.Mem (0x5000L, 8); _ }
        ->
          true
      | _ -> false );
    ( write 0x1000L,
      Compare.Write
        { pc = 0x1000L; addr = 0x5000L; size = 8; value = 43L; thread = 1 },
      function
      | Compare.Memory_value_mismatch
          { criterion = Compare.Mem (0x5000L, 8); _ } ->
          true
      | _ -> false );
  ]

let synthetic () =
  let differences =
    List.for_all event_differences ~f:(fun (left, right, expected) ->
        Compare.equal_result (Compare.compare [ left ] [ left ]) Compare.Equal
        && expected (reason (Compare.compare [ left ] [ right ])))
  in
  let thread =
    match
      reason
        (Compare.compare
           [ instruction 1L ]
           [ Compare.Instruction { pc = 1L; thread = 2 } ])
    with
    | Compare.Thread_mismatch { left = 1; right = 2 } -> true
    | _ -> false
  in
  let normalize =
    Compare.normalization
      ~address:(fun addr -> Int64.(addr land 0xfffL))
      ~value:(fun value -> Int64.(value % 4L))
      ()
  in
  let normalized =
    let left =
      Compare.Write
        { pc = 0x1010L; addr = 0x1500L; size = 4; value = 16L; thread = 1 }
    in
    let right =
      Compare.Write
        { pc = 0x9010L; addr = 0x9500L; size = 4; value = 20L; thread = 1 }
    in
    Compare.equal_result
      (Compare.compare ~normalize [ left ] [ right ])
      Compare.Equal
  in
  let left = List.init 7 ~f:(fun i -> instruction (Int64.of_int (i + 1))) in
  let right =
    List.mapi left ~f:(fun i event ->
        if i = 3 then instruction 40L
        else if i = 4 then instruction 50L
        else event)
  in
  let first_and_bounded =
    match Compare.compare ~context:2 left right with
    | Compare.Difference { index = 3; before; left; right; _ } ->
        let pcs =
          List.map ~f:(function Compare.Instruction { pc; _ } -> pc | _ -> 0L)
        in
        List.equal Int64.equal (pcs before) [ 2L; 3L ]
        && List.equal Int64.equal (pcs left) [ 4L; 5L ]
        && List.equal Int64.equal (pcs right) [ 40L; 50L ]
    | _ -> false
  in
  let missing =
    match Compare.compare ~context:2 (List.take left 3) (List.take left 5) with
    | Compare.Difference
        {
          index = 3;
          reason = Compare.Missing { side = Compare.Left; _ };
          before;
          left = [];
          right;
          _;
        } ->
        List.length before = 2 && List.length right = 2
    | _ -> false
  in
  printf
    "synthetic: differences %b, thread %b, normalized %b, windows %b, missing %b\n"
    differences thread normalized first_and_bounded missing

let engines echo =
  let run engine blocks =
    let emu = Emu.create ~engine ~args:[ "hi" ] (Bap_script.project echo) in
    let trace = Emu.Trace.start ~size:(1 lsl 16) ~blocks ~accesses:4096 emu in
    ignore (Emu.run emu);
    trace
  in
  List.iter [ false; true ] ~f:(fun blocks ->
      let left = run `Unicorn blocks and right = run `Lifted blocks in
      let equal (left, right) =
        Compare.equal_result (Compare.compare left right) Compare.Equal
      in
      let instructions = Compare.instructions left in
      let raw_blocks =
        (not blocks)
        ||
        let events = Compare.blocks left in
        List.is_empty (Compare.blocks ~thread:(-1) left)
        && (not (List.is_empty events))
        && List.for_all events ~f:(function
          | Compare.Block { size; thread = 1; _ } when size > 0 -> true
          | _ -> false)
      in
      printf
        "engines blocks %b: instructions %b, branches %b, calls %b, writes %b, \
         tids %b, raw blocks %b\n"
        blocks
        (equal (instructions, Compare.instructions right))
        (equal (Compare.branches left, Compare.branches right))
        (equal (Compare.calls left, Compare.calls right))
        (equal (Compare.writes left, Compare.writes right))
        (List.is_empty (Compare.instructions ~thread:(-1) left)
        && List.for_all instructions ~f:(function
          | Compare.Instruction { thread = 1; _ } -> true
          | _ -> false))
        raw_blocks)

let memory_and_capture prog =
  let emu = Emu.create ~args:[ "a"; "b" ] (Bap_script.project prog) in
  let sym name =
    List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
  in
  let entry = sym "s_bytes" and finish = sym "s_bytes_ret" in
  let capture = Emu.Trace.capture ~regs:[ "RDI"; "RSI" ] emu [ entry ] in
  ignore (Emu.run emu ~until:entry);
  let tid = Emu.thread emu in
  let trace = Emu.Trace.start ~blocks:true ~accesses:1024 emu in
  ignore (Emu.run emu ~until:finish);
  let captured =
    match Compare.captures ~thread:tid capture with
    | [ Compare.Capture { site; values = [ _; _ ]; thread } ] ->
        Int64.equal site entry && thread = tid
    | _ -> false
  in
  let written = List.last_exn (Compare.writes ~thread:tid trace) in
  let changed =
    match written with
    | Compare.Write event ->
        Compare.Write { event with value = Int64.(event.value + 1L) }
    | _ -> assert false
  in
  let sliced =
    match Compare.compare [ written ] [ changed ] with
    | Compare.Difference
        {
          reason =
            Compare.Memory_value_mismatch
              { criterion = Compare.Mem (addr, size); _ };
          _;
        } ->
        let slice = Emu.slice ~thread:tid trace [ Emu.Mem (addr, size) ] in
        not (List.is_empty slice.steps)
    | _ -> false
  in
  printf "capture %b, memory slice %b\n" captured sliced

let () =
  match Bap_script.args () with
  | [ echo; slice ] ->
      synthetic ();
      engines echo;
      memory_and_capture slice
  | _ -> failwith "expected ECHO SLICE"
