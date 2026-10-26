open Core
open Bap.Std
open Bap_primus.Std
module C = Bap_primus_native_plugin.Primus_native_checkpoint

module Snapshot_encoding = struct
  type descriptor = { name : string; addr : int; size : int }
  [@@deriving bin_io]

  type mem = {
    layers : unit list;
    values : (Addr.t * Word.t) list;
    generated : Addr.t list;
    protections : unit list;
  }
  [@@deriving bin_io]

  type t = { curr : descriptor; mems : (descriptor * mem) list }
  [@@deriving bin_io]
end

let check name condition = if not condition then failwith name
let saved = function Ok () -> () | Error msg -> failwith msg
let loaded = function Ok value -> value | Error msg -> failwith msg

let fails_with name substring = function
  | Ok _ -> failwith name
  | Error msg ->
      check
        (sprintf "%s: unexpected error %s" name msg)
        (String.is_substring (String.lowercase msg)
           ~substring:(String.lowercase substring))

let word value = Word.of_int64 ~width:64 value

let snapshot values =
  let descriptor = Snapshot_encoding.{ name = "test"; addr = 64; size = 8 } in
  let values =
    List.map values ~f:(fun (addr, value) -> (word addr, word value))
  in
  let encoded =
    Snapshot_encoding.
      {
        curr = descriptor;
        mems =
          [
            ( descriptor,
              { layers = []; values; generated = []; protections = [] } );
          ];
      }
  in
  Binable.of_string
    (module Primus.Memory.Snapshot)
    (Binable.to_string (module Snapshot_encoding) encoded)

let memory_values memory =
  Primus.Memory.Snapshot.values memory
  |> List.map ~f:(fun (addr, value) ->
      (Word.to_int64_exn addr, Word.to_int64_exn value))
  |> List.sort ~compare:(fun (x, _) (y, _) -> Int64.compare x y)

let checkpoint memory =
  {
    C.target = "bap:amd64";
    digest = "program-digest";
    pc = 0x400000L;
    frames =
      [
        { ret = 0x400100L; sp = 0x700000L; callee = Some "main"; caller = None };
      ];
    vars = [ (Var.create "R0" reg64_t, word 42L) ];
    memory;
    symbols = [ ("entry", 0x400000L) ];
    unstubbed = [ 0x400200L ];
    extensions = [ ("test:model", "saved-model-state") ];
    extra = [ (1, "extra-register") ];
    threads =
      Some
        {
          current = 2;
          cleared = Some 0x600000L;
          others = [];
          last = 2;
          woken = true;
        };
    model_states =
      Some [ { name = "test:model"; version = 3; required = true } ];
    thread_journal = [ { kind = "switch"; detail = "1 -> 2" } ];
    quantum_remaining = 0.0025;
  }

let read file = In_channel.read_all file

let with_restored_file file replacement f =
  let original = read file in
  Out_channel.write_all file ~data:replacement;
  Fun.protect f ~finally:(fun () -> Out_channel.write_all file ~data:original)

let () =
  let dir = Stdlib.Filename.temp_file "bap-native-checkpoint" "" in
  Caml_unix.unlink dir;
  Caml_unix.mkdir dir 0o700;
  let root = Filename.concat dir "root.ckpt" in
  let first = Filename.concat dir "first.ckpt" in
  let second = Filename.concat dir "second.ckpt" in
  let full = Filename.concat dir "full.ckpt" in
  let root_state = checkpoint (snapshot [ (0x1000L, 1L); (0x2000L, 2L) ]) in
  saved (C.save root root_state);
  check "full checkpoint magic changed"
    (String.is_prefix (read root) ~prefix:"bap-primus-unicorn-checkpoint 7\n");
  let first_state =
    {
      root_state with
      pc = 0x400010L;
      memory = snapshot [ (0x1000L, 3L); (0x2000L, 2L) ];
    }
  in
  saved (C.save ~parent:root first first_state);
  let second_state =
    {
      first_state with
      pc = 0x400020L;
      memory = snapshot [ (0x1000L, 3L); (0x2000L, 2L); (0x3000L, 4L) ];
    }
  in
  saved (C.save ~parent:first second second_state);
  check "delta checkpoint has full magic"
    (String.is_prefix (read second)
       ~prefix:"bap-primus-unicorn-checkpoint-delta 1\n");
  let restored = loaded (C.load second) in
  check "multi-link memory wasn't reconstructed"
    ([%equal: (int64 * int64) list]
       (memory_values restored.memory)
       [ (0x1000L, 3L); (0x2000L, 2L); (0x3000L, 4L) ]);
  check "delta lost the program counter" Int64.(restored.pc = second_state.pc);
  check "delta lost variables"
    (List.equal
       (fun (x, a) (y, b) -> Var.equal x y && Word.equal a b)
       restored.vars second_state.vars);
  check "delta lost frames" (Poly.equal restored.frames second_state.frames);
  check "delta lost thread state"
    (Poly.equal restored.threads second_state.threads);
  check "delta lost extensions"
    (Poly.equal restored.extensions second_state.extensions);
  check "delta lost models"
    (Poly.equal restored.model_states second_state.model_states);
  check "delta lost scheduler state"
    (Float.equal restored.quantum_remaining second_state.quantum_remaining);
  let chain = Bap_emu.Checkpoint.chain second in
  check "chain isn't root first"
    (List.equal String.equal
       (List.map chain ~f:(fun link -> link.Bap_emu.Checkpoint.file))
       [ root; first; second ]);
  check "chain has wrong versions"
    (List.equal Int.equal
       (List.map chain ~f:(fun link -> link.Bap_emu.Checkpoint.version))
       [ 7; 1; 1 ]);
  List.iter chain ~f:(fun link ->
      check "chain has wrong file digest"
        (String.equal link.Bap_emu.Checkpoint.digest (C.digest link.file)));
  check "chain lost parent linkage"
    (Option.equal
       (fun (path, digest) (path', digest') ->
         String.equal path path' && String.equal digest digest')
       (List.last_exn chain).parent
       (Some (first, C.digest first)));
  check "chain lost model metadata"
    (List.for_all chain ~f:(fun link ->
         match link.Bap_emu.Checkpoint.models with
         | Some [ { name = "test:model"; version = 3; required = true } ] ->
             true
         | _ -> false));

  saved (C.save full root_state);
  saved (C.save full { root_state with pc = 0xdeadbeefL });
  check "full checkpoint no longer replaces"
    Int64.((loaded (C.load full)).pc = 0xdeadbeefL);
  let before = read first in
  fails_with "delta overwrote an existing destination" "already exists"
    (C.save ~parent:root first second_state);
  check "failed delta publication changed its destination"
    (String.equal before (read first));

  let cwd = Caml_unix.getcwd () in
  Fun.protect
    ~finally:(fun () -> Caml_unix.chdir cwd)
    (fun () ->
      Caml_unix.chdir dir;
      let relative = "relative.ckpt" in
      saved (C.save ~parent:"root.ckpt" relative first_state);
      check "relative parent wasn't canonicalized"
        (String.equal
           (Option.value_exn
              (List.last_exn (Bap_emu.Checkpoint.chain relative)).parent
           |> fst)
           root));
  Caml_unix.rename root (root ^ ".away");
  fails_with "missing parent was accepted" "resolve" (C.load second);
  Caml_unix.rename (root ^ ".away") root;
  with_restored_file root (read full) (fun () ->
      fails_with "parent digest mismatch was accepted" "digest" (C.load second));
  with_restored_file root
    (String.sub (read root) ~pos:0 ~len:(String.length (read root) / 2))
    (fun () -> fails_with "truncated parent was accepted" "" (C.chain second));
  with_restored_file second
    (String.sub (read second) ~pos:0 ~len:(String.length (read second) / 2))
    (fun () ->
      fails_with "truncated delta was accepted" "broken" (C.load second));
  with_restored_file root (read first) (fun () ->
      fails_with "cyclic parent was accepted" "" (C.chain second));
  print_endline "native checkpoint deltas ok"
