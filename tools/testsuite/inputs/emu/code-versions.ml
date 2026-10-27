#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let code = 0x500000L
let ret = "\xc0\x03\x5f\xd6"
let check name ok = if not ok then failwith name

let protect ?(fresh = false) emu ~readable addr =
  Emu.primus emu
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax
                module Memory = Primus.Memory.Make (Machine)

                let init () =
                  let word = Word.of_int64 ~width:64 in
                  (if fresh then Memory.allocate (word addr) 0x1000
                   else Machine.return ())
                  >>= fun () ->
                  Memory.protect ~lower:(word addr)
                    ~upper:(word Int64.(addr + 0xfffL))
                    { readable; writable = readable; executable = true }
              end)

let expect_call stage emu addr =
  match Emu.call emu addr with
  | Some 0L -> ()
  | Some value -> failwithf "%s trampoline returned %Lx" stage value ()
  | None -> failwithf "%s trampoline paused" stage ()

let captured trace addr bytes =
  Emu.Trace.versions trace
  |> List.exists ~f:(fun (version : Emu.Trace.code_version) ->
      Int64.equal version.pc addr && String.is_prefix version.bytes ~prefix:bytes)

let decoded trace addr =
  Emu.Trace.inspect ~executed_bytes:true trace
  |> List.exists ~f:(fun (insn : Emu.Trace.window_instruction) ->
      Int64.equal insn.pc addr
      && match insn.decode with Decoded -> true | Decode_failed -> false)

let engine = function
  | "unicorn" -> `Unicorn
  | "lifted" -> `Lifted
  | name -> failwithf "unknown engine %s" name ()

let run file work kind blocks =
  let engine = engine kind in
  let project () = Bap_script.project file in
  let emu = Emu.create ~engine (project ()) in
  protect ~fresh:true emu ~readable:true code;
  Emu.write emu code ret;
  expect_call "initial" emu code;
  let checkpoint = Filename.concat work (sprintf "code-%s-%b.ckpt" kind blocks) in
  Emu.save emu checkpoint;
  let restored = Emu.create ~engine ~restore:checkpoint (project ()) in
  check "checkpoint lost the current trampoline bytes"
    (String.equal (Emu.read restored code 4) ret);
  protect restored ~readable:false code;
  check "execute-only page became readable"
    (match Emu.read restored code 4 with
    | _ -> false
    | exception Invalid_argument _ -> true);
  if Poly.equal engine `Lifted then
    check "restored history lost the trampoline bytes"
      (String.equal (Emu.lifted_bytes restored code 4) ret);
  let trace =
    if Poly.equal engine `Lifted then
      Some (Emu.Trace.start ~size:16 ~blocks ~code_versions:16 restored)
    else None
  in
  expect_call "traced" restored code;
  Option.iter trace ~f:(fun trace ->
      Emu.Trace.stop trace;
      check "executed trampoline bytes were not captured"
        (captured trace code ret);
      check "captured trampoline bytes do not decode" (decoded trace code));
  if Poly.equal engine `Lifted then begin
    let long_code = 0x501000L in
    let long_bytes =
      String.concat (List.init 200 ~f:(fun _ -> "\xe0\x03\x00\xaa")) ^ ret
    in
    protect ~fresh:true restored ~readable:true long_code;
    Emu.write restored long_code long_bytes;
    protect restored ~readable:false long_code;
    let trace = Emu.Trace.start ~size:16 ~blocks:true ~code_versions:16 restored in
    expect_call "long execute-only" restored long_code;
    Emu.Trace.stop trace;
    check "long execute-only block bytes were not captured"
      (captured trace long_code (String.prefix long_bytes 512));
    check "long execute-only block does not decode" (decoded trace long_code)
  end;
  printf "%s blocks %b: execute-only restore ok\n" kind blocks

let () =
  match Bap_script.args () with
  | [ file; work; kind; blocks ] -> run file work kind (Bool.of_string blocks)
  | _ -> failwith "expected PROGRAM WORK ENGINE BLOCKS"
