#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu
module C = Bap_primus_native_plugin.Primus_native_checkpoint

let model = "checkpoint-model"
let other = "checkpoint-other"

let register ?(required = true) ?(version = 1) name state =
  Emu.Checkpoint.register ~package:"test" ~required ~version name
    ~save:(fun () -> Some (Int.to_string !state))
    ~restore:(fun data -> state := Int.of_string data)

let pause_at_main emu =
  let main = List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main" in
  match Emu.run emu ~until:main with
  | Paused -> ()
  | _ -> failwith "can't pause at main"

let create ?restore file = Emu.create ?restore (Bap_script.project file)

let save file ckpt state =
  let emu = create file in
  pause_at_main emu;
  Emu.save emu ckpt;
  printf "saved %d\n" state

let show_status emu =
  match Emu.status emu with
  | Paused -> "paused"
  | Running -> "running"
  | Exited code ->
      sprintf "exited %s" (Option.value_map code ~default:"-" ~f:Int.to_string)
  | Failed msg -> sprintf "failed: %s" msg

let restore ?(required = true) ?(version = 1) ?(name = model) file ckpt state =
  register ~required ~version name state;
  let emu = create ~restore:ckpt file in
  printf "%s; model=%d\n" (show_status emu) !state

let write_legacy ckpt =
  let (cp : C.t) = Result.ok_or_failwith (C.load ckpt) in
  let legacy : C.V5.t =
    {
      target = cp.target;
      digest = cp.digest;
      pc = cp.pc;
      frames = cp.frames;
      vars = cp.vars;
      memory = cp.memory;
      symbols = cp.symbols;
      unstubbed = cp.unstubbed;
      extensions = cp.extensions;
      extra = cp.extra;
      threads = cp.threads;
    }
  in
  Out_channel.with_file ~binary:true ckpt ~f:(fun out ->
      Out_channel.output_string out C.magic5;
      Out_channel.output_string out (Binable.to_string (module C.V5) legacy));
  print_endline "converted to v5"

let rewrite_checkpoint ckpt f =
  let (cp : C.t) = Result.ok_or_failwith (C.load ckpt) in
  let cp = f cp in
  Out_channel.with_file ~binary:true ckpt ~f:(fun out ->
      Out_channel.output_string out C.magic;
      Out_channel.output_string out (Binable.to_string (module C.T) cp))

let corrupt_table ckpt =
  rewrite_checkpoint ckpt (fun cp ->
      {
        cp with
        extensions =
          List.map cp.extensions ~f:(fun (name, data) ->
              if String.equal name "test:table" then (name, "broken")
              else (name, data));
      });
  print_endline "corrupted table payload"

let duplicate_manifest ckpt =
  rewrite_checkpoint ckpt (fun cp ->
      match cp.model_states with
      | Some (model :: models) ->
          { cp with model_states = Some (model :: model :: models) }
      | _ -> failwith "empty manifest");
  match C.load ckpt with
  | Error msg -> printf "rejected: %s\n" msg
  | Ok _ -> print_endline "accepted duplicate manifest"

let show_models ckpt =
  match Emu.Checkpoint.models ckpt with
  | None -> print_endline "models: legacy"
  | Some models ->
      List.filter models ~f:(fun (m : Emu.Checkpoint.model_state) ->
          String.equal m.name ("test:" ^ model))
      |> List.iter ~f:(fun (m : Emu.Checkpoint.model_state) ->
          printf "model %s version=%d required=%b\n" m.name m.version m.required)

module Pair_list_binable = struct
  type t = (string * int) list

  let bin_shape_t =
    Bin_prot.Shape.bin_shape_list
      (Bin_prot.Shape.bin_shape_pair Bin_prot.Shape.bin_shape_string
         Bin_prot.Shape.bin_shape_int)

  let bin_size_t =
    Bin_prot.Size.bin_size_list
      (Bin_prot.Size.bin_size_pair Bin_prot.Size.bin_size_string
         Bin_prot.Size.bin_size_int)

  let bin_write_t =
    Bin_prot.Write.bin_write_list
      (Bin_prot.Write.bin_write_pair Bin_prot.Write.bin_write_string
         Bin_prot.Write.bin_write_int)

  let bin_read_t =
    Bin_prot.Read.bin_read_list
      (Bin_prot.Read.bin_read_pair Bin_prot.Read.bin_read_string
         Bin_prot.Read.bin_read_int)

  let __bin_read_t__ buf ~pos_ref _ = bin_read_t buf ~pos_ref
end

module Int_pair_list = struct
  type t = (string * int) list

  include
    Binable.Of_binable_with_uuid
      (Pair_list_binable)
      (struct
        type nonrec t = t

        let to_binable (value : t) : Pair_list_binable.t = value
        let of_binable (value : Pair_list_binable.t) : t = value

        let caller_identity =
          Bin_prot.Shape.Uuid.of_string "42ca824a-c27b-4fec-b5a4-e73dabc9d1ea"
      end)
end

let () =
  match Bap_script.args () with
  | [ "save"; file; ckpt; value ] ->
      let state = ref (Int.of_string value) in
      register model state;
      save file ckpt !state;
      show_models ckpt
  | [ "save-optional"; file; ckpt; value ] ->
      let state = ref (Int.of_string value) in
      register ~required:false model state;
      save file ckpt !state
  | [ "restore"; file; ckpt; required; version ] ->
      restore ~required:(Bool.of_string required)
        ~version:(Int.of_string version) file ckpt (ref 0)
  | [ "missing"; file; ckpt ] ->
      let emu = create ~restore:ckpt file in
      print_endline (show_status emu)
  | [ "save-none"; file; ckpt ] ->
      Out_channel.write_all ckpt ~data:"preserved";
      Emu.Checkpoint.register ~package:"test" ~required:true model
        ~save:(fun () -> None)
        ~restore:ignore;
      let emu = create file in
      pause_at_main emu;
      (match Emu.save emu ckpt with
      | exception Failure msg -> printf "save failed: %s\n" msg
      | () -> print_endline "save unexpectedly succeeded");
      printf "destination: %s\n" (In_channel.read_all ckpt)
  | [ "legacy"; ckpt ] -> write_legacy ckpt
  | [ "legacy-restore"; file; ckpt; required ] ->
      restore ~required:(Bool.of_string required) file ckpt (ref 0)
  | [ "helpers-save"; file; ckpt ] ->
      let state = ref 42 in
      let table = String.Table.create () in
      Hashtbl.set table ~key:"answer" ~data:43;
      Emu.Checkpoint.register_ref ~package:"test" ~required:true "ref"
        (module Int)
        state;
      Emu.Checkpoint.register_table ~package:"test" ~required:true "table"
        (module Int_pair_list)
        table;
      save file ckpt !state
  | [ "corrupt-helper"; ckpt ] -> corrupt_table ckpt
  | [ "duplicate-manifest"; ckpt ] -> duplicate_manifest ckpt
  | [ "helpers-restore"; file; ckpt ] ->
      let state = ref 0 in
      let table = String.Table.create () in
      Emu.Checkpoint.register_ref ~package:"test" ~required:true "ref"
        (module Int)
        state;
      Emu.Checkpoint.register_table ~package:"test" ~required:true "table"
        (module Int_pair_list)
        table;
      let emu = create ~restore:ckpt file in
      printf "%s; ref=%d; answer=%d; empty=%b\n" (show_status emu) !state
        (Option.value (Hashtbl.find table "answer") ~default:(-1))
        (Hashtbl.is_empty table)
  | [ "atomic-save"; file; ckpt ] ->
      register model (ref 41);
      register other (ref 42);
      save file ckpt 0
  | [ "atomic-restore"; file; ckpt ] ->
      let good = ref 0 in
      let bad = ref 0 in
      register ~version:1 model good;
      register ~version:2 other bad;
      let emu = create ~restore:ckpt file in
      printf "%s; good=%d; bad=%d\n" (show_status emu) !good !bad
  | [ "invalid-version"; version ] -> (
      match
        Emu.Checkpoint.register ~version:(Int.of_string version) model
          ~save:(fun () -> None)
          ~restore:ignore
      with
      | exception Invalid_argument msg -> print_endline msg
      | () -> print_endline "accepted invalid version")
  | _ -> failwith "invalid checkpoint-model test arguments"
