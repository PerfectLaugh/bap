open Core
open Bap.Std
module Engine = Bap_engine

let code = 0x1000L
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
        else if Int64.(addr = code + 1L) then
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

let () =
  exercise "unicorn" (Bap_engine_unicorn.create Engine.X86 Engine.Mode.mode32);
  exercise "lifted"
    (Bap_engine_lifted.create config Engine.X86 Engine.Mode.mode32);
  direct_unicorn ();
  direct_lifted ();
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
