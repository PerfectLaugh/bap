open Core
module Jni = Bap_emu.Jni

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

let make ?log ?versions () =
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
  ( Jni.create ~read_string ~alloc_string ~classes ~objects ?log ?versions (),
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

module Fake = struct
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

  let word emu address =
    let bytes = Stdlib.Bytes.create 8 in
    Stdlib.Bytes.blit_string (read emu address 8) 0 bytes 0 8;
    Stdlib.Bytes.get_int64_le bytes 0
end

module Adapter = Jni.Make (Fake)

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
  let emu = Fake.create () in
  Adapter.install jni emu layout;
  expect "vm table" layout.vm_functions (Fake.word emu layout.vm);
  expect "env table" layout.env_functions (Fake.word emu layout.env);
  expect "indexed env entry"
    Int64.(layout.env_stubs + (31L * 8L))
    (Fake.word emu Int64.(layout.env_functions + (31L * 8L)));
  Fake.set_reg emu "X8" 31L;
  Fake.set_reg emu "X1" (Jni.intern jni 0x1111L);
  Fake.set_reg emu "X30" 0x1234L;
  Adapter.serve jni emu;
  expect "serve class"
    (dispatch jni 31 [ 0L; Jni.intern jni 0x1111L ])
    (Fake.reg emu "X0");
  expect "serve return" 0x1234L (Fake.reg emu "PC");
  Fake.set_reg emu "X8" 6L;
  Fake.set_reg emu "X1" 0x5000L;
  Fake.set_reg emu "X2" 0x10006L;
  Adapter.serve_vm jni emu;
  expect "GetEnv status" 0L (Fake.reg emu "X0");
  expect "GetEnv output" layout.env (Fake.word emu 0x5000L);
  Fake.set_reg emu "X2" 0x10004L;
  Adapter.serve_vm jni emu;
  expect "GetEnv wrong version" (-2L) (Fake.reg emu "X0");
  Fake.set_reg emu "X8" 219L;
  Fake.set_reg emu "X1" 0x5008L;
  Adapter.serve jni emu;
  expect "GetJavaVM status" 0L (Fake.reg emu "X0");
  expect "GetJavaVM output" layout.vm (Fake.word emu 0x5008L);
  expect_string "adapter read_string" "hello"
    (Fake.write emu 0x16000L "hello\000ignored";
     Adapter.read_string emu 0x16000L)

let test_state () =
  let jni, address = make () in
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
  let restored, restored_address = make () in
  Jni.import_state restored saved;
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
  let before_invalid_import = Jni.export_state restored in
  (match Jni.import_state restored "broken" with
  | exception Invalid_argument _ -> ()
  | () -> failwith "invalid JNI state was accepted");
  expect_string "invalid import is atomic" before_invalid_import
    (Jni.export_state restored)

let test_stale_string_buffer () =
  let strings = Int64.Table.create () in
  let source = 0x9000L in
  let next = ref 0xa000L in
  Hashtbl.set strings ~key:source ~data:"created";
  let read_string address = Hashtbl.find_exn strings address in
  let alloc_string text =
    let address = !next in
    (next := Int64.(address + 0x100L));
    Hashtbl.set strings ~key:address ~data:text;
    address
  in
  let make_native () = Jni.create ~read_string ~alloc_string () in
  let jni = make_native () in
  let created = dispatch jni 167 [ 0L; source ] in
  let chars = dispatch jni 169 [ 0L; created ] in
  let saved = Jni.export_state jni in
  Hashtbl.set strings ~key:source ~data:"reused";
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
  let emu = Fake.create () in
  Adapter.install jni emu layout;
  List.iter versions ~f:(fun version ->
      Fake.set_reg emu "X8" 6L;
      Fake.set_reg emu "X1" 0x5000L;
      Fake.set_reg emu "X2" version;
      Adapter.serve_vm jni emu;
      expect "supported GetEnv version" 0L (Fake.reg emu "X0"));
  Fake.set_reg emu "X2" 0x10008L;
  Adapter.serve_vm jni emu;
  expect "unsupported GetEnv version" (-2L) (Fake.reg emu "X0");
  expect "reported JNI version" 0x10006L (dispatch jni 4 [])

let () =
  expect_string "last method table name" "GetObjectRefType"
    (Jni.name_of_index 232);
  expect_string "method table end" "JNIEnv[233]" (Jni.name_of_index 233);
  expect_string "method table name" "GetObjectClass" (Jni.name_of_index 31);
  expect_string "unknown method name" "JNIEnv[999]" (Jni.name_of_index 999);
  test_identity ();
  test_declarations_and_logging ();
  test_adapter ();
  test_state ();
  test_stale_string_buffer ();
  test_versions ();
  print_endline "JNI model tests passed"
