#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let entry = 0x400600L
let data = 0x601080L
let boundary = 0x70000000fff8L

let regular =
  String.concat
    [
      "\x48\xbb\x80\x10\x60\x00\x00\x00\x00\x00";
      "\x0f\xb6\x03";
      "\x0f\xb7\x43\x01";
      "\x8b\x43\x03";
      "\x48\x8b\x43\x07";
      "\x0f\xb6\x43\x0f";
      "\xf3\x0f\x6f\x43\x10";
      "\xc7\x43\x20\x78\x56\x34\x12";
    ]

let fault = "\x48\xb8\xf8\x1f\x60\x00\x00\x00\x00\x00\xf3\x0f\x6f\x00"
let stop = Int64.(entry + of_int (String.length regular))

let bytes =
  "\x80\x34\x80\x78\x56\x34\x80\xf0\xde\xbc\x9a\x78\x56\x34\x80\x00"
  ^ "\x01\x23\x45\x67\x89\xab\xcd\xef\x10\x32\x54\x76\x98\xba\xdc\xfe"

let expected engine =
  [
    (data, 1, false, Some 0x80L);
    (Int64.(data + 1L), 2, false, Some 0x8034L);
    (Int64.(data + 3L), 4, false, Some 0x80345678L);
    (Int64.(data + 7L), 8, false, Some 0x803456789abcdef0L);
    (Int64.(data + 15L), 1, false, Some 0L);
  ]
  @ (match engine with
    | `Unicorn ->
        [
          (Int64.(data + 16L), 8, false, Some 0xefcdab8967452301L);
          (Int64.(data + 24L), 8, false, Some 0xfedcba9876543210L);
        ]
    | `Lifted -> [ (Int64.(data + 16L), 16, false, None) ])
  @ [ (Int64.(data + 32L), 4, true, None) ]

let describe (addr, size, write, value) =
  sprintf "%Lx/%d/%s/%s" addr size (string_of_bool write)
    (Option.value_map value ~default:"-" ~f:(sprintf "%Lx"))

let check name expected actual =
  if not (Poly.equal expected actual) then
    failwithf "%s: expected %s, got %s" name
      (String.concat ~sep:" " (List.map expected ~f:describe))
      (String.concat ~sep:" " (List.map actual ~f:describe))
      ()

let allocate_page emu addr =
  Emu.primus emu
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax
                module Memory = Primus.Memory.Make (Machine)

                let init () =
                  Memory.allocate
                    (Word.of_int64 ~width:64 Int64.(addr land -4096L))
                    0x1000
              end)

let run ?read_values file engine blocks =
  let emu = Emu.create ~engine (Bap_script.project file) in
  allocate_page emu boundary;
  Emu.write emu entry (regular ^ "\x90" ^ fault);
  Emu.write emu data bytes;
  Emu.write emu boundary "\x00\x00\x00\x00\x00\x00\x00\x00";
  let trace = Emu.Trace.start ?read_values ~size:256 ~blocks ~accesses:64 emu in
  (match Emu.run emu ~until:stop with
  | Paused -> ()
  | _ -> failwith "the read-value program didn't pause before its fault");
  (match Emu.run emu with
  | Failed _ -> ()
  | _ -> failwith "the partial read didn't fault");
  Emu.Trace.accesses trace
  |> List.filter ~f:(fun (a : Emu.Trace.access) ->
         Int64.(
           (a.addr >= data && a.addr < data + 64L)
           || (a.addr >= boundary && a.addr <= boundary + 8L)))
  |> List.map ~f:(fun (a : Emu.Trace.access) ->
         (a.addr, a.size, a.write, a.read_value))

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  List.iter
    [ (`Unicorn, "unicorn"); (`Lifted, "lifted") ]
    ~f:(fun (engine, name) ->
      List.iter [ false; true ] ~f:(fun blocks ->
          check
            (sprintf "%s enabled" name)
            (expected engine)
            (run ~read_values:true file engine blocks);
          check
            (sprintf "%s disabled" name)
            (List.map (expected engine) ~f:(fun (addr, size, write, _) ->
                 (addr, size, write, None)))
            (run file engine blocks);
          printf "%s blocks %b: enabled and disabled read values are correct\n"
            name blocks))
