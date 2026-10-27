open Core
open Bap.Std
module Engine = Bap_engine

let code = 0x1000L
let second = 0x1001L
let finish = 0x1002L

let reg name =
  Option.value_exn
    (Engine.Register.by_name Engine.X86 ~bits:32 name)
    ~message:("no register " ^ name)
  |> fun r -> r.id

let check name expected got =
  if Int64.(expected <> got) then
    failwithf "%s: expected %Lx, got %Lx" name expected got ()

let ecx = Var.create "ECX" (Type.imm 32)
let edx = Var.create "EDX" (Type.imm 32)
let increment = Def.create ecx Bil.(var ecx + int (Word.one 32))
let decrement = Def.create edx Bil.(var edx - int (Word.one 32))

let config : Bap_engine_lifted.config =
  {
    lift =
      (fun ~thumb:_ addr _ ->
        if Int64.(addr = code) then
          Some (1, "INC", [ Blk.create ~defs:[ increment ] () ])
        else if Int64.(addr = second) then
          Some (1, "DEC", [ Blk.create ~defs:[ decrement ] () ])
        else None);
    name = (fun _ -> None);
    policy = 0;
    delay = (fun _ -> `None);
    locate =
      (fun name ->
        match name with
        | "ECX" | "EDX" | "EIP" -> Some (reg name, 0, 32)
        | _ -> None);
    owner = Option.some;
    pc = reg "EIP";
    big_endian = false;
    bits = 32;
    jit = false;
    cache = None;
  }

let layout_config arch bits pc : Bap_engine_lifted.config =
  {
    config with
    lift = (fun ~thumb:_ _ _ -> None);
    locate =
      (fun name ->
        Option.map (Engine.Register.by_name arch ~bits name) ~f:(fun r ->
            (r.id, 0, r.size * 8)));
    pc;
    bits;
  }

let check_bytes label expected got =
  if not (String.equal expected got) then
    failwithf "%s: register bytes differ" label ()

let compare_layouts label arch bits mode =
  let raw = Bap_unicorn.create arch mode in
  Exn.protect
    ~finally:(fun () -> Bap_unicorn.close raw)
    ~f:(fun () ->
      let regs = Bap_unicorn.regs arch in
      let pc = snd (List.hd_exn regs) in
      let lifted =
        Bap_engine_lifted.create (layout_config arch bits pc) arch mode
      in
      Exn.protect
        ~finally:(fun () -> Engine.close lifted)
        ~f:(fun () ->
          List.iter regs ~f:(fun (name, id) ->
              let expected = Bap_unicorn.reg_size raw id in
              let got = Engine.reg_size lifted id in
              if expected <> got then
                failwithf "%s: %s: expected width %d, got %d" label name
                  expected got ();
              let expected =
                if Poly.equal arch Engine.Arm64 && String.equal name "PSTATE"
                then Bap_unicorn.reg_read_bytes raw id
                else String.make expected '\000'
              in
              check_bytes
                (label ^ ":" ^ name)
                expected
                (Engine.reg_read_bytes lifted id));
          let id, size =
            List.fold regs ~init:(pc, 0)
              ~f:(fun ((_, best) as current) (_, id) ->
                let size = Bap_unicorn.reg_size raw id in
                if size > best then (id, size) else current)
          in
          let initial_raw = Bap_unicorn.reg_read_bytes raw id in
          let initial_lifted = Engine.reg_read_bytes lifted id in
          let saved_raw = Bap_unicorn.save raw in
          let saved_lifted = Engine.save lifted in
          let changed = String.make size '\x5a' in
          Bap_unicorn.reg_write_bytes raw id changed;
          Engine.reg_write_bytes lifted id changed;
          Bap_unicorn.restore raw saved_raw;
          Engine.restore saved_lifted;
          check_bytes (label ^ ":raw context") initial_raw
            (Bap_unicorn.reg_read_bytes raw id);
          check_bytes
            (label ^ ":lifted context")
            initial_lifted
            (Engine.reg_read_bytes lifted id)))

let exercise name engine =
  Exn.protect
    ~finally:(fun () -> Engine.close engine)
    ~f:(fun () ->
      Engine.mem_map engine code 0x1000L Engine.Perm.all;
      Engine.mem_write engine code "\x41\x4a";
      Engine.reg_write engine (reg "ECX") 0x1234L;
      Engine.reg_write engine (reg "EDX") 0x7890L;
      let calls = ref 0 in
      let hook = Engine.on_code engine (fun _ _ -> incr calls) in
      Engine.start engine code ~until:finish;
      check (name ^ " ecx") 0x1235L (Engine.reg_read engine (reg "ECX"));
      check (name ^ " edx") 0x788fL (Engine.reg_read engine (reg "EDX"));
      if !calls <> 2 then failwithf "%s: wrong hook count %d" name !calls ();
      let saved = Engine.save engine in
      Engine.reg_write engine (reg "ECX") 0L;
      Engine.restore saved;
      check (name ^ " restored") 0x1235L (Engine.reg_read engine (reg "ECX"));
      Engine.delete hook;
      Engine.flush_tb engine;
      Engine.start engine code ~until:finish;
      if !calls <> 2 then failwithf "%s: deleted hook ran" name ())

let direct_unicorn () =
  let module D = Bap_engine_unicorn.Direct in
  let engine = D.create Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> D.close engine)
    ~f:(fun () ->
      D.reg_write engine (reg "ECX") 42L;
      let saved = D.save engine in
      D.reg_write engine (reg "ECX") 0L;
      D.restore saved;
      check "direct unicorn" 42L (D.reg_read engine (reg "ECX"));
      D.delete (D.on_unsupported engine ignore))

let direct_lifted () =
  let module D = Bap_engine_lifted.Direct in
  let engine = D.create config Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> D.close engine)
    ~f:(fun () ->
      D.reg_write engine (reg "EDX") 42L;
      let saved = D.save engine in
      D.reg_write engine (reg "EDX") 0L;
      D.restore saved;
      check "direct lifted" 42L (D.reg_read engine (reg "EDX"));
      D.delete (D.on_unsupported engine ignore))

module Trace = Engine.Trace

let check_int name expected got =
  if not (Int.equal expected got) then
    failwithf "%s: expected %d, got %d" name expected got ()

let check_option name expected got =
  if not (Option.equal Int64.equal expected got) then
    failwithf "%s: wrong optional value" name ()

let state_ring () =
  let trace = Trace.create 1 in
  Trace.State.configure trace [ code; second ] [] [];
  Trace.set_thread trace 9;
  Trace.Record.record trace code 1 false;
  Trace.Record.capture trace code [||] [||];
  Trace.Record.unrun trace code;
  check_int "state unrun" 0 (List.length (Trace.State.records trace));
  Trace.Record.record trace code 1 false;
  Trace.Record.capture trace code [||] [||];
  Trace.Record.record trace second 1 false;
  Trace.Record.capture trace second [||] [||];
  match Trace.State.records trace with
  | [ r ] ->
      check "state retained site" second r.site;
      check "state retained index" 1L r.index;
      check_int "state retained thread" 9 r.thread;
      Trace.clear trace;
      check_int "state clear" 0 (List.length (Trace.State.records trace));
      check "state clear count" 0L (Trace.count trace)
  | rs ->
      failwithf "state ring: expected one record, got %d" (List.length rs) ()

let state name engine =
  Exn.protect
    ~finally:(fun () -> Engine.close engine)
    ~f:(fun () ->
      let data = 0x10000L in
      Engine.mem_map engine code 0x1000L Engine.Perm.all;
      Engine.mem_map engine data 0x1000L Engine.Perm.read;
      Engine.mem_map engine 0x20000L 0x1000L Engine.Perm.exec;
      Engine.mem_write engine code "\x41\x4a";
      Engine.mem_write engine data "\x11\x22\x33\x44";
      Engine.reg_write engine (reg "ECX") 0x1234L;
      Engine.reg_write engine (reg "EBX") data;
      let trace = Trace.create 16 in
      Trace.State.configure trace [ second; code ]
        [ (reg "ECX", 0, 4); (reg "EBX", 0, 3) ]
        [
          (reg "EBX", 0, 3, 1L, 2);
          (reg "EBX", 0, 4, 0x10000L, 4);
          (reg "EBX", 0, 4, 0xfffL, 2);
        ];
      let (_ : Engine.hook list) = Engine.trace engine trace in
      Engine.start engine code ~until:finish ~thread:7;
      (match Trace.State.records trace with
      | [ first; other ] ->
          check (name ^ " first site") code first.site;
          check (name ^ " second site") second other.site;
          check (name ^ " first index") 0L first.index;
          check (name ^ " second index") 1L other.index;
          check_int (name ^ " thread") 7 other.thread;
          check (name ^ " first pre-reg") 0x1234L first.regs.(0);
          check (name ^ " second pre-reg") 0x1235L other.regs.(0);
          check (name ^ " register slice") data other.regs.(1);
          check_option (name ^ " field") (Some 0x3322L) other.fields.(0);
          check_option (name ^ " denied field") None other.fields.(1);
          check_option (name ^ " partial field") None other.fields.(2)
      | rs ->
          failwithf "%s: expected two records, got %d" name (List.length rs) ());
      (match Trace.State.records ~last:1 trace with
      | [ r ] -> check (name ^ " last") second r.site
      | _ -> failwith (name ^ ": wrong last records"));
      Trace.clear trace;
      check_int (name ^ " clear") 0 (List.length (Trace.State.records trace)))

let state_jit () =
  let config = { config with jit = true } in
  let engine = Bap_engine_lifted.create config Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> Engine.close engine)
    ~f:(fun () ->
      Engine.mem_map engine code 0x1000L Engine.Perm.all;
      Engine.mem_write engine code "\x41\x4a";
      Engine.reg_write engine (reg "ECX") 0L;
      let trace = Trace.create 256 in
      Trace.State.configure trace [] [] [];
      let (_ : Engine.hook list) = Engine.trace engine trace in
      for _ = 1 to 40 do
        Engine.start engine code ~until:finish
      done;
      Trace.State.configure trace [ second ] [ (reg "ECX", 0, 4) ] [];
      Engine.start engine code ~until:finish;
      match Trace.State.records trace with
      | [ r ] ->
          check "state jit site" second r.site;
          check "state jit index" Int64.(Trace.count trace - 1L) r.index;
          check "state jit pre-reg" 41L r.regs.(0)
      | rs ->
          failwithf "state jit: expected one record, got %d" (List.length rs) ())

let check_poly name expected got =
  if not (Poly.equal expected got) then failwith (name ^ ": values differ")

let snapshot_block_trace () =
  let trace = Trace.create ~blocks:true ~accesses:3 ~read_values:true 3 in
  Trace.Record.prepare trace true;
  Trace.State.configure trace [ second; code ]
    [ (reg "ECX", 1, 4); (reg "EDX", 0, 8) ]
    [ (reg "EBX", 2, 4, 0x20L, 3); (reg "ECX", 0, 2, -4L, 8) ];
  Trace.set_thread trace 7;
  for i = 0 to 5 do
    let pc = if i mod 2 = 0 then code else second in
    Trace.Record.record trace pc (i + 1) (i mod 2 = 1);
    Trace.Record.extend trace 2;
    Trace.Record.access trace
      (i mod 2 = 0)
      (Int64.of_int (0x2000 + (8 * i)))
      (i + 1)
      (Int64.of_int (0x500 + i))
      (Int64.of_int (0x600 + i))
      pc;
    Trace.Record.access trace false 0x3000L 4 0x11223344L 0L pc;
    Trace.Record.capture trace pc
      [| Int64.of_int (0x10 + i); Int64.of_int (0x20 + i) |]
      [| Some (Int64.of_int (0x30 + i)); None |]
  done;
  Trace.Record.bound trace true true false 0L [| 0x4000L; 8L |] false;
  Trace.Record.bound trace false true false 0L [| 0x5000L; 16L |] false;
  Trace.set_thread trace 8;
  Trace.Record.bound trace true false false 0L [||] true;
  trace

let snapshot_round_trip () =
  let trace = snapshot_block_trace () in
  let snapshot = Trace.Snapshot.export trace in
  let restored = Trace.Snapshot.import snapshot in
  check_poly "snapshot round trip" snapshot (Trace.Snapshot.export restored);
  check "snapshot total count" 6L (Trace.count restored);
  check "snapshot access total" 12L (Trace.accesses_count restored);
  check_int "snapshot retained" 3 (Trace.retained restored);
  check_int "snapshot retained accesses" 3 (Trace.retained_accesses restored);
  check_int "snapshot retained captures" 3
    (List.length (Trace.State.records restored));
  check "snapshot bounds count" 2L snapshot.bounds_count;
  check "snapshot ranges count" 2L snapshot.ranges_count;
  check "snapshot sampling skip" 1L snapshot.skip;
  check "snapshot current thread" 8L snapshot.thread;
  check_poly "snapshot registers"
    (Trace.State.registers trace)
    (Trace.State.registers restored);
  check_poly "snapshot fields" (Trace.State.fields trace)
    (Trace.State.fields restored);
  check "snapshot unknown bound" (-1L) (Trace.bounds restored).{6};
  (match Trace.State.records restored with
  | first :: _ ->
      check "snapshot original capture index" 3L first.Trace.State.index;
      check "snapshot original capture site" second first.site;
      check_int "snapshot original capture thread" 7 first.thread
  | [] -> failwith "snapshot lost captures");
  let mutate trace pc value =
    Trace.set_thread trace 9;
    Trace.Record.record trace pc 4 true;
    Trace.Record.extend trace 3;
    Trace.Record.access trace true 0x6000L 8 value 0x77L pc;
    Trace.Record.capture trace pc
      [| value; Int64.neg value |]
      [| Some value; Some 0x55L |];
    Trace.Record.bound trace true true true pc [| 0x7000L; 2L |] false
  in
  mutate trace second 0x88L;
  mutate restored second 0x88L;
  check_poly "snapshot continued recording"
    (Trace.Snapshot.export trace)
    (Trace.Snapshot.export restored);
  match Trace.State.records restored with
  | [ _; _; last ] ->
      check "snapshot continued capture index" 6L last.index;
      check_int "snapshot continued capture thread" 9 last.thread
  | records ->
      failwithf "snapshot continuation kept %d captures" (List.length records)
        ()

let snapshot_sampling () =
  let trace = Trace.create ~every:3 4 in
  Trace.Record.record trace code 1 false;
  Trace.Record.record trace second 1 false;
  let snapshot = Trace.Snapshot.export trace in
  check "snapshot sampled count" 0L snapshot.count;
  check "snapshot sampled skip" 1L snapshot.skip;
  let restored = Trace.Snapshot.import snapshot in
  let record_both pc =
    Trace.Record.record trace pc 1 false;
    Trace.Record.record restored pc 1 false
  in
  record_both finish;
  record_both code;
  record_both second;
  record_both finish;
  check_poly "snapshot continued sampling"
    (Trace.Snapshot.export trace)
    (Trace.Snapshot.export restored);
  check "snapshot sampled total" 2L (Trace.count restored)

let snapshot_detached () =
  let snapshot = Trace.Snapshot.export (snapshot_block_trace ()) in
  let restored = Trace.Snapshot.import snapshot in
  let expected = Trace.Snapshot.export restored in
  snapshot.pcs.(0) <- 0xdeadL;
  snapshot.tids.(0) <- 0xbeefL;
  snapshot.capture_sites.(0) <- 0L;
  snapshot.capture_regs.(0) <- (1, 0, 1);
  let record = snapshot.captures.(0) in
  record.regs.(0) <- 0L;
  check_poly "snapshot detached import" expected
    (Trace.Snapshot.export restored);
  let exported = Trace.Snapshot.export restored in
  exported.capture_fields.(0) <- (1, 0, 1, 0L, 1);
  check_poly "snapshot detached export" expected
    (Trace.Snapshot.export restored)

let expect_bad_snapshot name snapshot =
  match Trace.Snapshot.import snapshot with
  | _ -> failwith (name ^ ": malformed snapshot was accepted")
  | exception Invalid_argument message ->
      if
        not
          (String.is_prefix message ~prefix:"Bap_native_trace.Snapshot.import")
      then failwith (name ^ ": unclear error: " ^ message)

let snapshot_malformed () =
  let valid = Trace.Snapshot.export (snapshot_block_trace ()) in
  expect_bad_snapshot "capacity" { valid with capacity = 3 };
  expect_bad_snapshot "allocation limit"
    { valid with capacity = 1 lsl 38; pcs = [||]; tids = [||] };
  expect_bad_snapshot "pcs" { valid with pcs = [||] };
  expect_bad_snapshot "sizes" { valid with sizes = [||] };
  expect_bad_snapshot "modes" { valid with modes = [| 0 |] };
  expect_bad_snapshot "invalid mode"
    { valid with modes = Array.copy valid.modes |> Array.map ~f:(fun _ -> 2) };
  expect_bad_snapshot "accesses" { valid with access_records = [||] };
  expect_bad_snapshot "bounds" { valid with bounds = [||] };
  expect_bad_snapshot "ranges" { valid with ranges = [||] };
  expect_bad_snapshot "negative count" { valid with count = -1L };
  expect_bad_snapshot "negative ranges" { valid with ranges_count = -1L };
  expect_bad_snapshot "sampling skip" { valid with skip = 0L };
  expect_bad_snapshot "capture count" { valid with captures_count = 0L };
  expect_bad_snapshot "capture register"
    { valid with capture_regs = [| (1, 0, 0); (2, 0, 4) |] };
  expect_bad_snapshot "capture field"
    { valid with capture_fields = [| (1, 0, 4, 0L, 9) |] };
  let bad_record = Array.copy valid.captures in
  bad_record.(0) <- { (bad_record.(0)) with regs = [||] };
  expect_bad_snapshot "capture record shape"
    { valid with captures = bad_record }

let () =
  exercise "unicorn" (Bap_engine_unicorn.create Engine.X86 Engine.Mode.mode32);
  exercise "lifted"
    (Bap_engine_lifted.create config Engine.X86 Engine.Mode.mode32);
  direct_unicorn ();
  direct_lifted ();
  state_ring ();
  state "unicorn" (Bap_engine_unicorn.create Engine.X86 Engine.Mode.mode32);
  state "lifted" (Bap_engine_lifted.create config Engine.X86 Engine.Mode.mode32);
  state_jit ();
  snapshot_round_trip ();
  snapshot_sampling ();
  snapshot_detached ();
  snapshot_malformed ();
  let engine = Bap_engine_unicorn.create Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> Engine.close engine)
    ~f:(fun () ->
      match Engine.taint_start engine with
      | exception Invalid_argument _ -> ()
      | () -> failwith "Unicorn unexpectedly propagated taint");
  List.iter
    [
      ("x86-16", Engine.X86, 16, Engine.Mode.mode16);
      ("x86-32", Engine.X86, 32, Engine.Mode.mode32);
      ("x86-64", Engine.X86, 64, Engine.Mode.mode64);
      ("arm", Engine.Arm, 32, Engine.Mode.(arm + little_endian));
      ("arm64-le", Engine.Arm64, 64, Engine.Mode.(arm + little_endian));
      ("arm64-be", Engine.Arm64, 64, Engine.Mode.(arm + big_endian));
      ("mips32", Engine.Mips, 32, Engine.Mode.(mips32 + little_endian));
      ("mips64", Engine.Mips, 64, Engine.Mode.(mips64 + little_endian));
      ("ppc32", Engine.Ppc, 32, Engine.Mode.(ppc32 + big_endian));
      ("ppc64", Engine.Ppc, 64, Engine.Mode.(ppc64 + big_endian));
      ("riscv32", Engine.Riscv, 32, Engine.Mode.riscv32);
      ("riscv64", Engine.Riscv, 64, Engine.Mode.riscv64);
    ]
    ~f:(fun (label, arch, bits, mode) -> compare_layouts label arch bits mode);
  print_endline "engine adapters: ok"
