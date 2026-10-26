open Core
open Bap.Std
module Engine = Bap_engine

let code = 0x1000L
let finish = 0x1002L

let reg name =
  Option.value_exn
    (Bap_engine_unicorn.reg Engine.X86 name)
    ~message:("no register " ^ name)

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

let exercise name uc =
  Exn.protect
    ~finally:(fun () -> Engine.close uc)
    ~f:(fun () ->
      Engine.mem_map uc code 0x1000L Engine.Perm.all;
      Engine.mem_write uc code "\x41\x4a";
      Engine.reg_write uc (reg "ECX") 0x1234L;
      Engine.reg_write uc (reg "EDX") 0x7890L;
      let calls = ref 0 in
      let hook = Engine.on_code uc (fun _ _ -> incr calls) in
      Engine.start uc code ~until:finish;
      check (name ^ " ecx") 0x1235L (Engine.reg_read uc (reg "ECX"));
      check (name ^ " edx") 0x788fL (Engine.reg_read uc (reg "EDX"));
      if !calls <> 2 then failwithf "%s: wrong hook count %d" name !calls ();
      let saved = Engine.save uc in
      Engine.reg_write uc (reg "ECX") 0L;
      Engine.restore saved;
      check (name ^ " restored") 0x1235L (Engine.reg_read uc (reg "ECX"));
      Engine.delete hook;
      Engine.flush_tb uc;
      Engine.start uc code ~until:finish;
      if !calls <> 2 then failwithf "%s: deleted hook ran" name ())

let direct_unicorn () =
  let module D = Bap_engine_unicorn.Direct in
  let uc = D.create Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> D.close uc)
    ~f:(fun () ->
      D.reg_write uc (reg "ECX") 42L;
      let saved = D.save uc in
      D.reg_write uc (reg "ECX") 0L;
      D.restore saved;
      check "direct unicorn" 42L (D.reg_read uc (reg "ECX"));
      D.delete (D.on_unsupported uc ignore))

let direct_lifted () =
  let module D = Bap_engine_lifted.Direct in
  let uc = D.create config Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> D.close uc)
    ~f:(fun () ->
      D.reg_write uc (reg "EDX") 42L;
      let saved = D.save uc in
      D.reg_write uc (reg "EDX") 0L;
      D.restore saved;
      check "direct lifted" 42L (D.reg_read uc (reg "EDX"));
      D.delete (D.on_unsupported uc ignore))

let () =
  exercise "unicorn" (Bap_engine_unicorn.create Engine.X86 Engine.Mode.mode32);
  exercise "lifted"
    (Bap_engine_lifted.create config Engine.X86 Engine.Mode.mode32);
  direct_unicorn ();
  direct_lifted ();
  let uc = Bap_engine_unicorn.create Engine.X86 Engine.Mode.mode32 in
  Exn.protect
    ~finally:(fun () -> Engine.close uc)
    ~f:(fun () ->
      match Engine.taint_start uc with
      | exception Invalid_argument _ -> ()
      | () -> failwith "Unicorn unexpectedly propagated taint");
  print_endline "engine adapters: ok"
