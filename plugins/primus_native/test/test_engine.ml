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
