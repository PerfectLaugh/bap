#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let check name ok = if not ok then failwith name
let pages = 64
let page_size = 0x1000
let code = 0x50000000L
let data = 0x60000000L
let data_size = pages * page_size

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
                  Memory.allocate (addr code) page_size >>= fun () ->
                  Memory.allocate (addr data) data_size >>= fun () ->
                  Memory.protect ~lower:(addr code)
                    ~upper:(addr Int64.(code + of_int page_size - 1L))
                    { readable = true; writable = true; executable = true }
              end)

let page n seed =
  String.init page_size ~f:(fun i ->
      Char.of_int_exn ((seed + (n * 17) + i) land 0xff))

let initial_page n = page n 1

let replace_data emu n contents =
  let offset = n * page_size in
  Emu.write emu Int64.(data + of_int offset) contents

let read_data emu =
  String.concat
    (List.init pages ~f:(fun n ->
         let offset = n * page_size in
         Emu.read emu Int64.(data + of_int offset) page_size))
let initial_data = String.concat (List.init pages ~f:initial_page)

let expected_data n contents =
  let prefix = n * page_size in
  String.concat
    [
      String.sub initial_data ~pos:0 ~len:prefix;
      contents;
      String.sub initial_data ~pos:(prefix + page_size)
        ~len:(data_size - prefix - page_size);
    ]

let primus_byte emu addr =
  let result = ref None in
  Emu.primus emu
    (module functor
              (Machine : Primus.Machine.S)
              ->
              struct
                open Machine.Syntax
                module Memory = Primus.Memory.Make (Machine)

                let init () =
                  Memory.load (Word.of_int64 ~width:64 addr) >>| fun value ->
                  result := Some (Word.to_int_exn value)
              end);
  Option.value_exn !result

let check_data name emu expected =
  let actual = read_data emu in
  if not (String.equal actual expected) then begin
    let i = ref 0 in
    while
      !i < String.length actual && !i < String.length expected
      && Char.equal actual.[!i] expected.[!i]
    do
      incr i
    done;
    let provenance =
      match Emu.provenance emu Int64.(data + of_int !i) with
      | Emu.Stored -> "stored"
      | Emu.Generated -> "generated"
      | Emu.Mapped -> "mapped"
      | Emu.Unmapped -> "unmapped"
    in
    let addr = Int64.(data + of_int !i) in
    failwithf
      "%s: first difference %d, actual %d expected %d, Primus %d, provenance \
       %s, lengths %d/%d"
      name !i
      (if !i < String.length actual then Char.to_int actual.[!i] else -1)
      (if !i < String.length expected then Char.to_int expected.[!i] else -1)
      (primus_byte emu addr) provenance (String.length actual)
      (String.length expected) ()
  end

let create ?(models = Emu.Checkpoint.create ()) ~engine ?restore file =
  Emu.create ~models ~engine ?restore (Bap_script.project file)

let pause_at_main emu =
  let main = List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main" in
  match Emu.run emu ~until:main with
  | Emu.Paused -> ()
  | _ -> failwith "didn't pause at main"

let prepare ~engine file =
  let emu = create ~engine file in
  pause_at_main emu;
  allocate emu;
  List.iter (List.init pages ~f:Fn.id) ~f:(fun n ->
      replace_data emu n (initial_page n));
  check_data "initial memory differs before saving" emu initial_data;
  Emu.write emu code "\x48\x8b\x07\x48\x03\x47\x08\xc3";
  emu

let execute emu =
  let changed = Int64.(data + (17L * of_int page_size)) in
  match Emu.call emu code ~args:[ changed ] with
  | Some value -> value
  | None -> failwith "restored execution didn't return"

let file_size file = (Caml_unix.stat file).st_size
let read_file file = In_channel.read_all file

let write_file file contents = Out_channel.write_all file ~data:contents

let restore_error ~models ~engine file checkpoint =
  try
    let emu = create ~models ~engine ~restore:checkpoint file in
    match Emu.status emu with Emu.Failed msg -> Some msg | _ -> None
  with exn -> Some (Exn.to_string exn)

let expect_restore_failure ?reason name ~models ~engine file checkpoint =
  match restore_error ~models ~engine file checkpoint with
  | None -> failwith name
  | Some error -> (
      match reason with
      | None -> ()
      | Some reason ->
          check name
            (String.is_substring (String.lowercase error)
               ~substring:(String.lowercase reason)))

let expect_chain_failure name checkpoint =
  match Emu.Checkpoint.chain checkpoint with
  | exception _ -> ()
  | _ -> failwith name

let with_replaced_file file replacement f =
  let original = read_file file in
  write_file file replacement;
  Fun.protect f ~finally:(fun () -> write_file file original)

let registry ?(version = 1) ?(required = true) ?(fail_save = ref false) state =
  let models = Emu.Checkpoint.create () in
  Emu.Checkpoint.register ~package:"test" ~required ~version models "delta"
    ~save:(fun () ->
      if !fail_save then failwith "intentional model save failure"
      else Some !state)
    ~restore:(fun saved -> state := saved);
  models

let run ~engine ~name file dir =
  let path leaf = Filename.concat dir (name ^ "-" ^ leaf) in
  let root = path "root.ckpt"
  and delta = path "delta.ckpt"
  and full = path "full.ckpt"
  and first = path "first.ckpt"
  and second = path "second.ckpt" in
  let emu = prepare ~engine file in
  Emu.save emu root;
  replace_data emu 17 (page 17 101);
  Emu.save emu ~parent:root delta;
  Emu.save emu full;
  let full_size = file_size full and delta_size = file_size delta in
  check "delta isn't materially smaller than a full checkpoint"
    (delta_size * 2 < full_size);
  let from_full = create ~engine ~restore:full file
  and from_delta = create ~engine ~restore:delta file in
  let expected = expected_data 17 (page 17 101) in
  check_data "full checkpoint restored different memory" from_full expected;
  check_data "delta restored different memory" from_delta expected;
  check "full and delta execution differ"
    (Int64.equal (execute from_full) (execute from_delta));

  let first_emu = create ~engine ~restore:root file in
  replace_data first_emu 3 (page 3 201);
  Emu.save first_emu ~parent:root first;
  let second_emu = create ~engine ~restore:root file in
  replace_data second_emu 3 (page 3 301);
  Emu.save second_emu ~parent:root second;
  let restored_first = create ~engine ~restore:first file
  and restored_second = create ~engine ~restore:second file in
  check_data "first child includes a sibling's changes" restored_first
    (expected_data 3 (page 3 201));
  check_data "second child includes a sibling's changes" restored_second
    (expected_data 3 (page 3 301));

  let root_contents = read_file root in
  Caml_unix.rename root (path "root-away.ckpt");
  Fun.protect
    (fun () ->
      expect_restore_failure "missing parent was accepted"
        ~models:(Emu.Checkpoint.create ()) ~engine file first)
    ~finally:(fun () -> Caml_unix.rename (path "root-away.ckpt") root);
  check "missing fixture damaged the root"
    (String.equal root_contents (read_file root));
  with_replaced_file root (read_file full) (fun () ->
      expect_restore_failure ~reason:"digest" "wrong parent digest was accepted"
        ~models:(Emu.Checkpoint.create ()) ~engine file first);
  with_replaced_file root
    (String.sub root_contents ~pos:0 ~len:(String.length root_contents / 2))
    (fun () -> expect_chain_failure "truncated ancestor was accepted" first);
  with_replaced_file root (read_file first) (fun () ->
      expect_chain_failure "cyclic chain was accepted" first);

  let model_root = path "model-root.ckpt"
  and model_child = path "model-child.ckpt" in
  let fail_save = ref false and state = ref "root" in
  let models = registry ~required:false ~fail_save state in
  let model_emu = create ~models ~engine file in
  pause_at_main model_emu;
  Emu.save model_emu model_root;
  let child = create ~engine ~restore:model_root file in
  Emu.save child ~parent:model_root model_child;
  expect_restore_failure ~reason:"schema version"
    "ancestor model schema mismatch was accepted"
    ~models:(registry ~version:2 (ref ""))
    ~engine file model_child;
  let before = read_file model_root in
  (match Emu.save model_emu ~parent:model_root model_root with
  | exception _ -> ()
  | () -> failwith "self-overwrite unexpectedly succeeded");
  check "self-overwrite changed its parent"
    (String.equal before (read_file model_root));
  fail_save := true;
  (match Emu.save model_emu ~parent:model_root model_root with
  | exception _ -> ()
  | () -> failwith "failed self-overwrite unexpectedly succeeded");
  check "failed self-overwrite changed its parent"
    (String.equal before (read_file model_root));
  ignore (Emu.Checkpoint.info model_root);

  let chain = Emu.Checkpoint.chain first in
  check "chain isn't root-first"
    (List.equal String.equal
       (List.map chain ~f:(fun link -> link.Emu.Checkpoint.file))
       [ root; first ]);
  printf "%s: delta %d/%d bytes; checkpoint delta ok\n" name delta_size
    full_size

let () =
  match Bap_script.args () with
  | [ file; dir ] ->
      run ~engine:`Unicorn ~name:"unicorn" file dir;
      run ~engine:`Lifted ~name:"lifted" file dir
  | _ -> failwith "expected ECHO DIR"
