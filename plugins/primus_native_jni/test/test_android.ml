open Core
module Android = Bap_emu.Android
module Jni = Bap_emu.Jni

let args values =
  let result = Array.create ~len:8 0L in
  List.iteri values ~f:(fun index value -> result.(index) <- value);
  result

let dispatch jni index values = Jni.dispatch jni { index; args = args values }

let expect label expected actual =
  if not (Int64.equal expected actual) then
    failwithf "%s: expected %Lx, got %Lx" label expected actual ()

let expect_string label expected actual =
  if not (String.equal expected actual) then
    failwithf "%s: expected %s, got %s" label expected actual ()

let service =
  {
    Android.name = "demo";
    identity = 0x1000L;
    class_name = "example/Demo";
    transact =
      (fun code request reply ->
        expect "transaction code" 7L code;
        expect_string "interface token" "demo.token"
          (Android.read_interface_token request |> Option.value_exn);
        expect "request integer" 42L
          (Android.read_int request |> Option.value_exn |> Int64.of_int32);
        Android.write_int reply 42l;
        Android.set_exception reply 0l);
  }

let make () =
  let environment = Android.create ~services:[ service ] () in
  let strings = Int64.Table.create () in
  let next = ref 0x7000L in
  List.iter
    [
      "android/os/ServiceManager";
      "android/os/Parcel";
      "android/os/IBinder";
      "example/Demo";
      "getService";
      "(Ljava/lang/String;)Landroid/os/IBinder;";
      "obtain";
      "()Landroid/os/Parcel;";
      "writeInterfaceToken";
      "(Ljava/lang/String;)V";
      "writeInt";
      "(I)V";
      "readException";
      "()V";
      "transact";
      "(ILandroid/os/Parcel;Landroid/os/Parcel;I)Z";
      "demo";
      "demo.token";
    ] ~f:(fun text ->
      let address = !next in
      (next := Int64.(address + 0x100L));
      Hashtbl.set strings ~key:address ~data:text);
  let read_string address = Hashtbl.find_exn strings address in
  let alloc_string text =
    let address = !next in
    (next := Int64.(address + 0x100L));
    Hashtbl.set strings ~key:address ~data:text;
    address
  in
  let address text =
    Hashtbl.to_alist strings
    |> List.find_map ~f:(fun (address, value) ->
        if String.equal text value then Some address else None)
    |> Option.value_exn
  in
  let jni =
    Jni.create ~read_string ~alloc_string
      ~class_of:(Android.class_of environment)
      ~classes:(Android.jni_classes environment)
      ()
  in
  (environment, jni, address)

let test_direct () =
  let environment = Android.create ~services:[ service ] () in
  let request = Android.obtain environment in
  Android.write_interface_token request "demo.token";
  Android.write_int request 42l;
  let reply = Android.obtain environment in
  expect "direct transact" 0L
    (Android.transact environment 0x1000L 7L request reply);
  expect "direct reply" 42L
    (Android.read_int reply |> Option.value_exn |> Int64.of_int32);
  expect "direct exception" 0L (Int64.of_int32 (Android.read_exception reply));
  let unknown = Android.obtain environment in
  expect "unknown binder" (-1L)
    (Android.transact environment 0xdeadL 7L request unknown);
  expect "unknown binder exception" (-1L)
    (Int64.of_int32 (Android.read_exception unknown))

let test_jni () =
  let environment, jni, address = make () in
  ignore environment;
  let find_class name = dispatch jni 6 [ 0L; address name ] in
  let java_string text = dispatch jni 167 [ 0L; address text ] in
  let instance_method class_handle name signature =
    dispatch jni 33 [ 0L; class_handle; address name; address signature ]
  in
  let static_method class_handle name signature =
    dispatch jni 113 [ 0L; class_handle; address name; address signature ]
  in
  let manager = find_class "android/os/ServiceManager" in
  let get_service =
    static_method manager "getService"
      "(Ljava/lang/String;)Landroid/os/IBinder;"
  in
  let binder =
    dispatch jni 114 [ 0L; manager; get_service; java_string "demo" ]
  in
  expect "service identity" 0x1000L (Jni.identity jni binder |> Option.value_exn);
  expect "service return class"
    (find_class "example/Demo")
    (dispatch jni 31 [ 0L; binder ]);
  expect "unknown service" 0L
    (dispatch jni 114 [ 0L; manager; get_service; java_string "demo.token" ]);
  let parcel_class = find_class "android/os/Parcel" in
  let obtain = static_method parcel_class "obtain" "()Landroid/os/Parcel;" in
  let request = dispatch jni 114 [ 0L; parcel_class; obtain ] in
  let reply = dispatch jni 114 [ 0L; parcel_class; obtain ] in
  if Int64.equal request reply then failwith "obtain reused a parcel identity";
  expect "parcel return class" parcel_class (dispatch jni 31 [ 0L; request ]);
  expect "parcel return class is shared" parcel_class
    (dispatch jni 31 [ 0L; reply ]);
  let write_token =
    instance_method parcel_class "writeInterfaceToken" "(Ljava/lang/String;)V"
  in
  let write_int = instance_method parcel_class "writeInt" "(I)V" in
  let read_exception = instance_method parcel_class "readException" "()V" in
  ignore
    (dispatch jni 63 [ 0L; request; write_token; java_string "demo.token" ]);
  ignore (dispatch jni 63 [ 0L; request; write_int; 42L ]);
  let binder_class = find_class "android/os/IBinder" in
  let transact =
    instance_method binder_class "transact"
      "(ILandroid/os/Parcel;Landroid/os/Parcel;I)Z"
  in
  expect "JNI transact" 1L
    (dispatch jni 37 [ 0L; binder; transact; 7L; request; reply; 0L ]);
  expect "JNI exception" 0L (dispatch jni 63 [ 0L; reply; read_exception ]);
  (environment, Jni.identity jni reply |> Option.value_exn)

let test_state () =
  let environment, reply_identity = test_jni () in
  let saved = Android.export_state environment in
  let restored = Android.create ~services:[ service ] () in
  Android.import_state restored saved;
  let restored_reply =
    Android.find_parcel restored reply_identity |> Option.value_exn
  in
  expect "restored reply" 42L
    (Android.read_int restored_reply |> Option.value_exn |> Int64.of_int32);
  expect "restored exception" 0L
    (Int64.of_int32 (Android.read_exception restored_reply));
  expect_string "restored service class" "example/Demo"
    (Android.class_of restored 0x1000L |> Option.value_exn);
  let fresh = Android.obtain restored in
  if Int64.equal (Android.parcel_identity fresh) reply_identity then
    failwith "restored identity cursor aliases an existing parcel";
  let missing = Android.create () in
  match Android.import_state missing saved with
  | exception Invalid_argument _ -> ()
  | () -> failwith "state with missing service declarations was accepted"

let () =
  test_direct ();
  test_state ();
  print_endline "Android model tests passed"
