#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let code = 0x500000L
let data = 0x600000L
let unmapped = 0x700000L
let sizes = [ 1; 2; 4; 8 ]
let check name ok = if not ok then failwith name

let allocate emu =
  Emu.primus emu
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax
                module Memory = Primus.Memory.Make (Machine)

                let init () =
                  let addr = Word.of_int64 ~width:64 in
                  Memory.allocate (addr code) 0x1000 >>= fun () ->
                  Memory.allocate (addr data) 0x10000 >>= fun () ->
                  Memory.protect ~lower:(addr code)
                    ~upper:(addr Int64.(code + 0xfffL))
                    { readable = true; writable = true; executable = true }
              end)

let protect_unreadable emu =
  Emu.primus emu
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax
                module Memory = Primus.Memory.Make (Machine)

                let init () =
                  let addr = Word.of_int64 ~width:64 in
                  List.fold sizes ~init:(Machine.return ())
                    ~f:(fun before size ->
                      before >>= fun () ->
                      let offset = (size / 2 * 0x2000) + 0x1000 in
                      let base = Int64.(data + of_int offset) in
                      Memory.protect ~lower:(addr base)
                        ~upper:(addr Int64.(base + 0xfffL))
                        {
                          readable = false;
                          writable = false;
                          executable = false;
                        })
              end)

let bytes size =
  match size with
  | 1 -> "\x11"
  | 2 -> "\x22\x33"
  | 4 -> "\x44\x55\x66\x77"
  | 8 -> "\x88\x77\x66\x55\x44\x33\x22\x11"
  | _ -> assert false

let value size =
  match size with
  | 1 -> 0x11L
  | 2 -> 0x3322L
  | 4 -> 0x77665544L
  | 8 -> 0x1122334455667788L
  | _ -> assert false

let page_offset size = size / 2 * 0x2000
let page_base size = Int64.(data + of_int (page_offset size))

let fields =
  List.concat_map sizes ~f:(fun size ->
      let page = page_offset size in
      [
        ("X1", Int64.of_int (page + 0x1000 - size), size);
        ("X1", Int64.of_int (page + 0x1001 - size), size);
        ("X1", Int64.of_int (page + 0x1000), size);
        ("X2", 0L, size);
      ])

let field_ok (state : Emu.Trace.state) (base, offset, size) =
  let valid_offset = Int64.of_int (page_offset size + 0x1000 - size) in
  let expected =
    if String.equal base "X1" && Int64.equal offset valid_offset then
      Some (value size)
    else None
  in
  List.exists state.fields ~f:(fun (field : Emu.Trace.state_field) ->
      String.equal field.base base
      && Int64.equal field.offset offset
      && field.size = size
      && Option.equal Int64.equal field.value expected)

let reg state name =
  List.Assoc.find_exn state.Emu.Trace.regs ~equal:String.equal name

let run file dir engine name =
  let emu = Emu.create ~engine (Bap_script.project file) in
  allocate emu;
  List.iter sizes ~f:(fun size ->
      Emu.write emu
        Int64.(page_base size + (0x1000L - of_int size))
        (bytes size));
  protect_unreadable emu;
  (* nop; add x0, x0, #1; nop; ret *)
  Emu.write emu code
    "\x1f\x20\x03\xd5\x00\x04\x00\x91\x1f\x20\x03\xd5\xc0\x03\x5f\xd6";
  let first = Emu.spawn_thread emu ~start:code ~arg:0L in
  let second = Emu.spawn_thread emu ~start:code ~arg:0L in
  let capture =
    Emu.Trace.capture_state ~size:16 ~regs:[ "X0"; "X1"; "X2" ] ~fields emu
      [ code; Int64.(code + 8L) ]
  in
  let bases = [ ("X1", data); ("X2", unmapped) ] in
  List.iter
    [ (first, 1L); (second, 2L) ]
    ~f:(fun (thread, arg) ->
      match Emu.drive emu code ~thread ~args:[ arg ] ~regs:bases with
      | Returned value ->
          check "captured call returned" Int64.(value = arg + 1L)
      | Parked _ -> failwith "captured call parked"
      | Ended _ -> failwith "captured call ended");
  let states = Emu.Trace.captured_states capture in
  check "captured four states" (List.length states = 4);
  let expected =
    [
      (first, code, 1L);
      (first, Int64.(code + 8L), 2L);
      (second, code, 2L);
      (second, Int64.(code + 8L), 3L);
    ]
  in
  List.iter2_exn states expected ~f:(fun state (thread, site, x0) ->
      check "captured the effective thread" (state.thread = thread);
      check "captured the site" Int64.(state.site = site);
      check "captured the pre-instruction register" Int64.(reg state "X0" = x0);
      check "captured every requested field"
        (List.length state.fields = List.length fields
        && List.for_all fields ~f:(field_ok state)));
  List.iter
    (List.zip_exn (List.drop_last_exn states) (List.tl_exn states))
    ~f:(fun (before, after) ->
      check "capture indices increase globally"
        Int64.(before.index < after.index));
  check "last states are the newest"
    (Poly.equal
       (Emu.Trace.captured_states ~last:2 capture)
       (List.drop states 2));
  let saved = Filename.concat dir (name ^ "-states.bin") in
  Emu.Trace.save_states capture saved;
  let loaded = Emu.Trace.load_states saved in
  check "state capture binary roundtrip" (Poly.equal loaded states);
  Emu.Trace.stop_state_capture capture;
  (match Emu.drive emu code ~thread:first ~args:[ 9L ] with
  | Returned 10L -> ()
  | _ -> failwith "call after capture stopped failed");
  check "stop_state_capture stops recording"
    (List.length (Emu.Trace.captured_states capture) = 4);
  List.iter loaded ~f:(fun state ->
      let x0 = reg state "X0" in
      let expected =
        if Int64.equal state.site code then Int64.(x0 + 1L) else x0
      in
      match Emu.drive emu state.site ~thread:state.thread ~regs:state.regs with
      | Returned value ->
          check "replayed captured thread and registers"
            Int64.(value = expected)
      | Parked _ -> failwith "replayed state parked"
      | Ended _ -> failwith "replayed state ended");
  printf "%s: capture state ok\n" name

let () =
  match Bap_script.args () with
  | [ file; dir ] ->
      run file dir `Unicorn "unicorn";
      run file dir `Lifted "lifted"
  | _ -> failwith "expected AARCH64-SPAWN DIR"
