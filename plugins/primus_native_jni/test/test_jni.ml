open Core
open Bap.Std
module Dis = Disasm_expert.Basic
module Jni = Bap_emu.Jni
module AArch64 = Bap_emu.AArch64

let fail label expected actual =
  failwithf "%s: expected %s, got %s" label expected actual ()

let expect label expected actual =
  if not (Int64.equal expected actual) then
    fail label (sprintf "%Lx" expected) (sprintf "%Lx" actual)

let expect_int label expected actual =
  if expected <> actual then
    fail label (Int.to_string expected) (Int.to_string actual)

let expect_string label expected actual =
  if not (String.equal expected actual) then fail label expected actual

let expect_failure label fragments f =
  match f () with
  | exception Failure msg ->
      List.iter fragments ~f:(fun fragment ->
          if not (String.is_substring msg ~substring:fragment) then
            failwithf "%s: missing %s in %s" label fragment msg ())
  | () -> failwith (label ^ ": expected a replay mismatch")
  | exception exn -> failwith (label ^ ": " ^ Exn.to_string exn)

let args values =
  let result = Array.create ~len:8 0L in
  List.iteri values ~f:(fun index value -> result.(index) <- value);
  result

let dispatch jni index values = Jni.dispatch jni { index; args = args values }

let methods =
  [
    {
      Jni.name = "isDirectory";
      signature = "()Z";
      answer = (fun _ _ -> Value 0L);
    };
  ]

let classes =
  [
    {
      Jni.name = "com/example/Example";
      methods;
      static_methods =
        [
          {
            name = "answer";
            signature = "()I";
            answer = (fun _ _ -> Value 42L);
          };
        ];
      fields =
        [
          {
            name = "packageName";
            signature = "Ljava/lang/String;";
            value = String "com.example.app";
          };
        ];
      static_fields =
        [ { name = "versionCode"; signature = "J"; value = Value 58L } ];
    };
  ]

let objects =
  [
    {
      Jni.identity = 0x1111L;
      class_name = "com/example/Example";
      elements = [ String "first"; Object 0x2222L ];
    };
  ]

let make ?log ?versions ?default () =
  let strings = Int64.Table.create () in
  let next_string = ref 0x7000L in
  List.iter
    [
      "com/example/Example";
      "isDirectory";
      "()Z";
      "answer";
      "()I";
      "packageName";
      "Ljava/lang/String;";
      "versionCode";
      "J";
      "created";
    ] ~f:(fun text ->
      let address = !next_string in
      (next_string := Int64.(address + 0x100L));
      Hashtbl.set strings ~key:address ~data:text);
  let read_string address = Hashtbl.find_exn strings address in
  let alloc_string text =
    let address = !next_string in
    (next_string := Int64.(address + 0x100L));
    Hashtbl.set strings ~key:address ~data:text;
    address
  in
  let address text =
    Hashtbl.to_alist strings
    |> List.find_map ~f:(fun (address, value) ->
        if String.equal text value then Some address else None)
    |> Option.value_exn
  in
  ( Jni.create ~read_string ~alloc_string ~classes ~objects ?log ?versions
      ?default (),
    address )

let test_identity () =
  let jni, _ = make () in
  let object_handle = Jni.intern jni 0x1111L in
  expect "intern is stable" object_handle (Jni.intern jni 0x1111L);
  let class_handle = dispatch jni 31 [ 0L; object_handle ] in
  expect "class handle is stable" class_handle
    (dispatch jni 31 [ 0L; object_handle ]);
  let global = dispatch jni 21 [ 0L; object_handle ] in
  expect "global handle is stable" global
    (dispatch jni 21 [ 0L; object_handle ]);
  expect "local/global identity" 1L
    (dispatch jni 24 [ 0L; object_handle; global ]);
  let class_global = dispatch jni 21 [ 0L; class_handle ] in
  expect "class/global identity" 1L
    (dispatch jni 24 [ 0L; class_handle; class_global ]);
  ignore (dispatch jni 22 [ 0L; global ]);
  expect "deleted global is not recycled" global
    (Jni.intern ~global:true jni 0x1111L);
  let other = Jni.intern jni 0x2222L in
  expect "different objects" 0L (dispatch jni 24 [ 0L; global; other ]);
  expect "null identity" 1L (dispatch jni 24 [ 0L; 0L; 0L ]);
  expect "null versus object" 0L (dispatch jni 24 [ 0L; 0L; global ]);
  expect "null intern" 0L (Jni.intern jni 0L);
  expect "identity lookup" 0x1111L (Jni.identity jni global |> Option.value_exn)

let test_declarations_and_logging () =
  let records = ref [] in
  let jni, address =
    make ~log:(fun record -> records := record :: !records) ()
  in
  let class_handle = dispatch jni 6 [ 0L; address "com/example/Example" ] in
  let method_handle =
    dispatch jni 33 [ 0L; class_handle; address "isDirectory"; address "()Z" ]
  in
  expect "declared method" 0L (dispatch jni 34 [ 0L; 0x1111L; method_handle ]);
  let static_method =
    dispatch jni 113 [ 0L; class_handle; address "answer"; address "()I" ]
  in
  expect "declared static method" 42L
    (dispatch jni 129 [ 0L; class_handle; static_method ]);
  let field =
    dispatch jni 94
      [ 0L; class_handle; address "packageName"; address "Ljava/lang/String;" ]
  in
  let package = dispatch jni 95 [ 0L; 0x1111L; field ] in
  expect "string field length" 15L (dispatch jni 168 [ 0L; package ]);
  let chars = dispatch jni 169 [ 0L; package ] in
  expect "string chars are stable" chars (dispatch jni 169 [ 0L; package ]);
  let static_field =
    dispatch jni 144 [ 0L; class_handle; address "versionCode"; address "J" ]
  in
  expect "static field" 58L
    (dispatch jni 151 [ 0L; class_handle; static_field ]);
  let created = dispatch jni 167 [ 0L; address "created" ] in
  let created_again = dispatch jni 167 [ 0L; address "created" ] in
  if Int64.equal created created_again then
    failwith "NewStringUTF reused a string identity";
  expect "new string length" 7L (dispatch jni 168 [ 0L; created ]);
  expect "array length" 2L (dispatch jni 171 [ 0L; 0x1111L ]);
  ignore (dispatch jni 173 [ 0L; 0x1111L; 0L ]);
  expect "array object identity" 1L
    (dispatch jni 24
       [ 0L; Jni.intern jni 0x2222L; dispatch jni 173 [ 0L; 0x1111L; 1L ] ]);
  let array = dispatch jni 172 [ 0L; 2L; class_handle; class_handle ] in
  expect "new array length" 2L (dispatch jni 171 [ 0L; array ]);
  expect "new array initial identity" 1L
    (dispatch jni 24 [ 0L; class_handle; dispatch jni 173 [ 0L; array; 0L ] ]);
  let record =
    List.find_exn !records ~f:(fun record -> record.call.index = 173)
  in
  expect_string "logged method name" "GetObjectArrayElement" record.name;
  expect "logged result" record.result (dispatch jni 173 [ 0L; array; 0L ]);
  expect_int "logged index" 173 record.call.index;
  expect "default answer" 0x99L
    (Jni.dispatch
       (Jni.create ~default:(fun _ _ -> Value 0x99L) ())
       { index = 999; args = args [] })

module Test_emulator = struct
  type t = { regs : int64 String.Table.t; memory : (int64, char) Hashtbl.t }

  let create () =
    { regs = String.Table.create (); memory = Hashtbl.Poly.create () }

  let read emu address size =
    String.init size ~f:(fun offset ->
        Option.value
          (Hashtbl.find emu.memory Int64.(address + of_int offset))
          ~default:'\000')

  let write emu address data =
    String.iteri data ~f:(fun offset byte ->
        Hashtbl.set emu.memory ~key:Int64.(address + of_int offset) ~data:byte)

  let reg emu name = Option.value (Hashtbl.find emu.regs name) ~default:0L
  let set_reg emu name value = Hashtbl.set emu.regs ~key:name ~data:value
  let set_pc emu value = set_reg emu "PC" value
  let event _ _ = ()

  let word emu address =
    let bytes = Stdlib.Bytes.create 8 in
    Stdlib.Bytes.blit_string (read emu address 8) 0 bytes 0 8;
    Stdlib.Bytes.get_int64_le bytes 0
end

module Adapter = Jni.Make (Test_emulator)

let decode_backward_branch emu at target =
  let data = Test_emulator.read emu at 4 in
  let mem =
    Memory.create LittleEndian
      (Addr.of_int64 ~width:64 at)
      (Bigstring.of_string data)
    |> Or_error.ok_exn
  in
  Dis.with_disasm ~backend:"llvm" "aarch64" ~f:(fun dis ->
      match Dis.insn_of_mem dis mem |> Or_error.ok_exn with
      | _, Some insn, _ ->
          expect_string
            (sprintf "JNI opcode at %Lx" at)
            "B" (Dis.Insn.name insn);
          let operand =
            Dis.Insn.ops insn |> Array.to_list |> List.map ~f:Op.to_string
            |> List.hd_exn |> Int64.of_string
          in
          expect
            (sprintf "JNI backward target at %Lx" at)
            target
            Int64.(at + (operand * 4L));
          Or_error.return ()
      | _, None, _ -> Or_error.errorf "failed to decode JNI branch at %Lx" at)
  |> Or_error.ok_exn

let expect_invalid label f =
  match f () with
  | exception Invalid_argument _ -> ()
  | exception exn -> failwith (label ^ ": " ^ Exn.to_string exn)
  | _ -> failwith (label ^ ": invalid encoding was accepted")

let test_aarch64_encoding () =
  expect_string "RET bytes" "\xc0\x03\x5f\xd6" (AArch64.bytes AArch64.ret);
  expect "branch to self" 0x14000000L
    (Int64.of_int32 (AArch64.b ~pc:0x1000L 0x1000L));
  expect "backward branch" 0x17ffffffL
    (Int64.of_int32 (AArch64.b ~pc:0x1000L 0xffcL));
  ignore (AArch64.b ~pc:0L (-0x8000000L));
  ignore (AArch64.b ~pc:0L 0x7fffffcL);
  expect_invalid "unaligned branch PC" (fun () -> AArch64.b ~pc:1L 0L);
  expect_invalid "unaligned branch target" (fun () -> AArch64.b ~pc:0L 1L);
  expect_invalid "positive branch overflow" (fun () ->
      AArch64.b ~pc:0L 0x8000000L);
  expect_invalid "negative branch overflow" (fun () ->
      AArch64.b ~pc:0L (-0x8000004L))

let layout =
  {
    Jni.vm = 0x1000L;
    vm_functions = 0x2000L;
    env = 0x3000L;
    env_functions = 0x4000L;
    env_stubs = 0x8000L;
    env_dispatcher = 0x7000L;
    vm_stubs = 0xa000L;
    vm_dispatcher = 0x9000L;
  }

let test_adapter () =
  let jni, _ = make () in
  let emu = Test_emulator.create () in
  Adapter.install jni emu layout;
  decode_backward_branch emu Int64.(layout.env_stubs + 4L) layout.env_dispatcher;
  decode_backward_branch emu Int64.(layout.vm_stubs + 4L) layout.vm_dispatcher;
  expect "vm table" layout.vm_functions (Test_emulator.word emu layout.vm);
  expect "env table" layout.env_functions (Test_emulator.word emu layout.env);
  expect "indexed env entry"
    Int64.(layout.env_stubs + (31L * 8L))
    (Test_emulator.word emu Int64.(layout.env_functions + (31L * 8L)));
  Test_emulator.set_reg emu "X8" 31L;
  Test_emulator.set_reg emu "X1" (Jni.intern jni 0x1111L);
  Test_emulator.set_reg emu "X30" 0x1234L;
  Adapter.serve jni emu;
  expect "serve class"
    (dispatch jni 31 [ 0L; Jni.intern jni 0x1111L ])
    (Test_emulator.reg emu "X0");
  expect "serve return" 0x1234L (Test_emulator.reg emu "PC");
  Test_emulator.set_reg emu "X8" 6L;
  Test_emulator.set_reg emu "X1" 0x5000L;
  Test_emulator.set_reg emu "X2" 0x10006L;
  Adapter.serve_vm jni emu;
  expect "GetEnv status" 0L (Test_emulator.reg emu "X0");
  expect "GetEnv output" layout.env (Test_emulator.word emu 0x5000L);
  Test_emulator.set_reg emu "X2" 0x10004L;
  Adapter.serve_vm jni emu;
  expect "GetEnv wrong version" (-2L) (Test_emulator.reg emu "X0");
  List.iter [ 4; 7 ] ~f:(fun index ->
      let output = Int64.(0x5010L + of_int Int.(index * 8)) in
      Test_emulator.set_reg emu "X8" (Int64.of_int index);
      Test_emulator.set_reg emu "X1" output;
      Adapter.serve_vm jni emu;
      expect
        (sprintf "attach status at index %d" index)
        0L
        (Test_emulator.reg emu "X0");
      expect
        (sprintf "attach output at index %d" index)
        layout.env
        (Test_emulator.word emu output));
  Test_emulator.set_reg emu "X8" 219L;
  Test_emulator.set_reg emu "X1" 0x5008L;
  Adapter.serve jni emu;
  expect "GetJavaVM status" 0L (Test_emulator.reg emu "X0");
  expect "GetJavaVM output" layout.vm (Test_emulator.word emu 0x5008L);
  expect_string "adapter read_string" "hello"
    (Test_emulator.write emu 0x16000L "hello\000ignored";
     Adapter.read_string emu 0x16000L)

let test_state () =
  let jni, address = make () in
  Jni.start_recording jni;
  let class_handle = dispatch jni 6 [ 0L; address "com/example/Example" ] in
  let method_handle =
    dispatch jni 33 [ 0L; class_handle; address "isDirectory"; address "()Z" ]
  in
  let field_handle =
    dispatch jni 94
      [ 0L; class_handle; address "packageName"; address "Ljava/lang/String;" ]
  in
  let object_handle = Jni.intern jni 0x1111L in
  let global = dispatch jni 21 [ 0L; object_handle ] in
  let created = dispatch jni 167 [ 0L; address "created" ] in
  let created_again = dispatch jni 167 [ 0L; address "created" ] in
  let chars = dispatch jni 169 [ 0L; created ] in
  let array = dispatch jni 172 [ 0L; 2L; class_handle; class_handle ] in
  let other_array = dispatch jni 172 [ 0L; 1L; class_handle; 0L ] in
  let string_class = dispatch jni 31 [ 0L; created ] in
  let array_class = dispatch jni 31 [ 0L; array ] in
  expect "string classes before export" string_class
    (dispatch jni 31 [ 0L; created_again ]);
  expect "array classes before export" array_class
    (dispatch jni 31 [ 0L; other_array ]);
  let saved = Jni.export_state jni in
  let saved_events = Jni.journal jni in
  let restored, restored_address = make () in
  Jni.import_state restored saved;
  if not (Poly.equal saved_events (Jni.journal restored)) then
    failwith "restored JNI journal differs";
  expect "restored class" class_handle
    (dispatch restored 6 [ 0L; restored_address "com/example/Example" ]);
  expect "restored method" method_handle
    (dispatch restored 33
       [
         0L;
         class_handle;
         restored_address "isDirectory";
         restored_address "()Z";
       ]);
  expect "restored field" field_handle
    (dispatch restored 94
       [
         0L;
         class_handle;
         restored_address "packageName";
         restored_address "Ljava/lang/String;";
       ]);
  expect "restored global" global (dispatch restored 21 [ 0L; object_handle ]);
  expect "restored string length" 7L (dispatch restored 168 [ 0L; created ]);
  expect "restored second string length" 7L
    (dispatch restored 168 [ 0L; created_again ]);
  expect "restored string address" chars (dispatch restored 169 [ 0L; created ]);
  expect "restored array length" 2L (dispatch restored 171 [ 0L; array ]);
  expect "restored array element" class_handle
    (dispatch restored 173 [ 0L; array; 0L ]);
  expect "restored string class" string_class
    (dispatch restored 31 [ 0L; created_again ]);
  expect "restored array class" array_class
    (dispatch restored 31 [ 0L; other_array ]);
  let next_string = dispatch restored 167 [ 0L; restored_address "created" ] in
  if Int64.equal next_string created || Int64.equal next_string created_again
  then failwith "restored model recycled a string handle";
  let next_object = Jni.intern restored 0x3333L in
  if Int64.equal next_object object_handle || Int64.equal next_object global
  then failwith "restored model recycled an object handle";
  let restored_events = Jni.journal restored in
  expect_int "restored JNI ordinal"
    (List.length restored_events)
    (List.last_exn restored_events).ordinal;
  let before_invalid_import = Jni.export_state restored in
  (match Jni.import_state restored "broken" with
  | exception Invalid_argument _ -> ()
  | () -> failwith "invalid JNI state was accepted");
  expect_string "invalid import is atomic" before_invalid_import
    (Jni.export_state restored);
  let mismatched = Jni.create ~classes:(List.tl_exn classes) () in
  let before_mismatch = Jni.export_state mismatched in
  (match Jni.import_state mismatched saved with
  | exception Invalid_argument msg ->
      if not (String.is_substring msg ~substring:"declaration fingerprint") then
        failwith msg
  | () -> failwith "mismatched JNI declarations were accepted");
  expect_string "mismatched import is atomic" before_mismatch
    (Jni.export_state mismatched)

let test_replay () =
  let jni, address = make () in
  let emu = Test_emulator.create () in
  Adapter.install jni emu layout;
  Jni.start_recording jni;
  let class_handle = dispatch jni 6 [ 0L; address "com/example/Example" ] in
  let method_handle =
    dispatch jni 33 [ 0L; class_handle; address "isDirectory"; address "()Z" ]
  in
  ignore method_handle;
  let created = dispatch jni 167 [ 0L; address "created" ] in
  let array = dispatch jni 172 [ 0L; 2L; class_handle; created ] in
  ignore array;
  Test_emulator.set_reg emu "X8" 4L;
  Test_emulator.set_reg emu "X1" 0x5000L;
  Adapter.serve_vm jni emu;
  ignore (Jni.dispatch jni { index = 999; args = args [] });
  Jni.stop_recording jni;
  let events = Jni.export_journal (Jni.journal jni) |> Jni.import_journal in
  expect_int "recorded operations" 6 (List.length events);
  let created_event = List.nth_exn events 2 in
  expect_int "recorded string argument" 1 (List.length created_event.strings);
  expect_string "recorded string value" "created"
    (snd (List.hd_exn created_event.strings));
  let vm_event = List.nth_exn events 4 in
  if not (Poly.equal vm_event.kind Jni.JavaVM) then
    failwith "JavaVM event has the wrong kind";
  let fresh, _ = make () in
  Jni.start_recording fresh;
  Jni.replay fresh events;
  Jni.stop_recording fresh;
  expect_int "replay does not append" 0 (List.length (Jni.journal fresh));
  let change ordinal f =
    List.map events ~f:(fun (event : Jni.event) ->
        if event.ordinal = ordinal then f event else event)
  in
  let wrong_kind = change 1 (fun event -> { event with kind = Jni.JavaVM }) in
  expect_failure "wrong operation kind"
    [ "ordinal 1"; "FindClass"; "JavaVM.GetEnv" ] (fun () ->
      let model, _ = make () in
      Jni.replay model wrong_kind);
  let wrong_result =
    change 1 (fun event -> { event with result = Int64.(event.result + 0x10L) })
  in
  expect_failure "wrong result" [ "ordinal 1"; "expected result"; "got result" ]
    (fun () ->
      let model, _ = make () in
      Jni.replay model wrong_result);
  let wrong_identity =
    change 1 (fun event -> { event with result_identity = Some (Internal 999) })
  in
  expect_failure "wrong identity"
    [
      "ordinal 1";
      "result identity internal 999";
      "got result identity internal 0";
    ] (fun () ->
      let model, _ = make () in
      Jni.replay model wrong_identity);
  let wrong_detail =
    change 2 (fun event -> { event with detail = Some "wrong detail" })
  in
  expect_failure "wrong detail"
    [ "ordinal 2"; "GetMethodID"; "wrong detail"; "isDirectory" ] (fun () ->
      let model, _ = make () in
      Jni.replay model wrong_detail);
  expect_failure "wrong default result"
    [ "ordinal 6"; "JNIEnv[999]"; "result 0x0"; "result 0x99" ] (fun () ->
      let model, _ = make ~default:(fun _ _ -> Value 0x99L) () in
      Jni.replay model events);
  expect_failure "wrong starting ordinal"
    [ "expected ordinal 1"; "got ordinal 2" ] (fun () ->
      let model, _ = make () in
      ignore (Jni.dispatch model { index = 999; args = args [] });
      Jni.replay model events);
  match Jni.import_journal "broken" with
  | exception Invalid_argument _ -> ()
  | _ -> failwith "invalid journal was accepted"

let test_stale_string_buffer () =
  let strings = Int64.Table.create () in
  let source = 0x9000L in
  Hashtbl.set strings ~key:source ~data:"created";
  let read_string address = Hashtbl.find_exn strings address in
  let make_native () =
    let next = ref 0xa000L in
    let alloc_string text =
      let address = !next in
      (next := Int64.(address + 0x100L));
      Hashtbl.set strings ~key:address ~data:text;
      address
    in
    Jni.create ~read_string ~alloc_string ()
  in
  let jni = make_native () in
  Jni.start_recording jni;
  let created = dispatch jni 167 [ 0L; source ] in
  let chars = dispatch jni 169 [ 0L; created ] in
  Jni.stop_recording jni;
  let journal = Jni.export_journal (Jni.journal jni) |> Jni.import_journal in
  let saved = Jni.export_state jni in
  Hashtbl.set strings ~key:source ~data:"reused";
  let replayed = make_native () in
  Jni.replay replayed journal;
  expect "replayed saved string" 7L (dispatch replayed 168 [ 0L; created ]);
  let restored = make_native () in
  Jni.import_state restored saved;
  expect "saved content, not current pointer" 7L
    (dispatch restored 168 [ 0L; created ]);
  expect "saved native string address" chars
    (dispatch restored 169 [ 0L; created ]);
  let reused = dispatch restored 167 [ 0L; source ] in
  expect "reused buffer has its new content" 6L
    (dispatch restored 168 [ 0L; reused ])

let test_versions () =
  let versions = [ 0x10002L; 0x10004L; 0x10006L ] in
  let jni, _ = make ~versions () in
  let emu = Test_emulator.create () in
  Adapter.install jni emu layout;
  List.iter versions ~f:(fun version ->
      Test_emulator.set_reg emu "X8" 6L;
      Test_emulator.set_reg emu "X1" 0x5000L;
      Test_emulator.set_reg emu "X2" version;
      Adapter.serve_vm jni emu;
      expect "supported GetEnv version" 0L (Test_emulator.reg emu "X0"));
  Test_emulator.set_reg emu "X2" 0x10008L;
  Adapter.serve_vm jni emu;
  expect "unsupported GetEnv version" (-2L) (Test_emulator.reg emu "X0");
  expect "reported JNI version" 0x10006L (dispatch jni 4 [])

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () ->
      expect_string "last method table name" "GetObjectRefType"
        (Jni.name_of_index 232);
      expect_string "method table end" "JNIEnv[233]" (Jni.name_of_index 233);
      expect_string "method table name" "GetObjectClass" (Jni.name_of_index 31);
      expect_string "unknown method name" "JNIEnv[999]" (Jni.name_of_index 999);
      test_identity ();
      test_declarations_and_logging ();
      test_aarch64_encoding ();
      test_adapter ();
      test_state ();
      test_replay ();
      test_stale_string_buffer ();
      test_versions ();
      print_endline "JNI model tests passed"
