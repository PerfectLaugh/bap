open Core

type object_id = int64
type call = { index : int; args : int64 array }

type answer =
  | Value of int64
  | Object of object_id
  | String of string
  | Handle of int64
  | Fresh

type handler = t -> call -> answer
and method_decl = { name : string; signature : string; answer : handler }
and field_decl = { name : string; signature : string; value : answer }

and class_decl = {
  name : string;
  methods : method_decl list;
  static_methods : method_decl list;
  fields : field_decl list;
  static_fields : field_decl list;
}

and object_decl = {
  identity : object_id;
  class_name : string;
  elements : answer list;
}

and call_record = {
  call : call;
  name : string;
  detail : string option;
  result : int64;
}

and identity = External of int64 | Internal of int
and ref_kind = Local | Global | Weak
and method_info = { method_decl : method_decl; owner : identity; static : bool }
and field_info = { field_decl : field_decl; owner : identity; static : bool }
and string_info = { content : string; mutable address : int64 option }

and t = {
  mutable next_handle : int64;
  mutable next_identity : int;
  handles : (ref_kind * identity, int64) Hashtbl.t;
  sources : (int64, identity) Hashtbl.t;
  classes : (string, identity) Hashtbl.t;
  class_names : (identity, string) Hashtbl.t;
  object_classes : (identity, identity) Hashtbl.t;
  arrays : (identity, answer list) Hashtbl.t;
  methods : (identity, method_info) Hashtbl.t;
  method_ids : (identity * string * string * bool, identity) Hashtbl.t;
  fields : (identity, field_info) Hashtbl.t;
  field_ids : (identity * string * string * bool, identity) Hashtbl.t;
  strings : (identity, string_info) Hashtbl.t;
  strings_by_content : (string, identity) Hashtbl.t;
  read_string : (int64 -> string) option;
  alloc_string : (string -> int64) option;
  class_of : object_id -> string option;
  default : handler;
  version : int64;
  log : (call_record -> unit) option;
  mutable env : int64;
  mutable vm : int64;
}

let arg call n = if n < Array.length call.args then call.args.(n) else 0L

let names =
  [|
    "reserved0";
    "reserved1";
    "reserved2";
    "reserved3";
    "GetVersion";
    "DefineClass";
    "FindClass";
    "FromReflectedMethod";
    "FromReflectedField";
    "ToReflectedMethod";
    "GetSuperclass";
    "IsAssignableFrom";
    "ToReflectedField";
    "Throw";
    "ThrowNew";
    "ExceptionOccurred";
    "ExceptionDescribe";
    "ExceptionClear";
    "FatalError";
    "PushLocalFrame";
    "PopLocalFrame";
    "NewGlobalRef";
    "DeleteGlobalRef";
    "DeleteLocalRef";
    "IsSameObject";
    "NewLocalRef";
    "EnsureLocalCapacity";
    "AllocObject";
    "NewObject";
    "NewObjectV";
    "NewObjectA";
    "GetObjectClass";
    "IsInstanceOf";
    "GetMethodID";
    "CallObjectMethod";
    "CallObjectMethodV";
    "CallObjectMethodA";
    "CallBooleanMethod";
    "CallBooleanMethodV";
    "CallBooleanMethodA";
    "CallByteMethod";
    "CallByteMethodV";
    "CallByteMethodA";
    "CallCharMethod";
    "CallCharMethodV";
    "CallCharMethodA";
    "CallShortMethod";
    "CallShortMethodV";
    "CallShortMethodA";
    "CallIntMethod";
    "CallIntMethodV";
    "CallIntMethodA";
    "CallLongMethod";
    "CallLongMethodV";
    "CallLongMethodA";
    "CallFloatMethod";
    "CallFloatMethodV";
    "CallFloatMethodA";
    "CallDoubleMethod";
    "CallDoubleMethodV";
    "CallDoubleMethodA";
    "CallVoidMethod";
    "CallVoidMethodV";
    "CallVoidMethodA";
    "CallNonvirtualObjectMethod";
    "CallNonvirtualObjectMethodV";
    "CallNonvirtualObjectMethodA";
    "CallNonvirtualBooleanMethod";
    "CallNonvirtualBooleanMethodV";
    "CallNonvirtualBooleanMethodA";
    "CallNonvirtualByteMethod";
    "CallNonvirtualByteMethodV";
    "CallNonvirtualByteMethodA";
    "CallNonvirtualCharMethod";
    "CallNonvirtualCharMethodV";
    "CallNonvirtualCharMethodA";
    "CallNonvirtualShortMethod";
    "CallNonvirtualShortMethodV";
    "CallNonvirtualShortMethodA";
    "CallNonvirtualIntMethod";
    "CallNonvirtualIntMethodV";
    "CallNonvirtualIntMethodA";
    "CallNonvirtualLongMethod";
    "CallNonvirtualLongMethodV";
    "CallNonvirtualLongMethodA";
    "CallNonvirtualFloatMethod";
    "CallNonvirtualFloatMethodV";
    "CallNonvirtualFloatMethodA";
    "CallNonvirtualDoubleMethod";
    "CallNonvirtualDoubleMethodV";
    "CallNonvirtualDoubleMethodA";
    "CallNonvirtualVoidMethod";
    "CallNonvirtualVoidMethodV";
    "CallNonvirtualVoidMethodA";
    "GetFieldID";
    "GetObjectField";
    "GetBooleanField";
    "GetByteField";
    "GetCharField";
    "GetShortField";
    "GetIntField";
    "GetLongField";
    "GetFloatField";
    "GetDoubleField";
    "SetObjectField";
    "SetBooleanField";
    "SetByteField";
    "SetCharField";
    "SetShortField";
    "SetIntField";
    "SetLongField";
    "SetFloatField";
    "SetDoubleField";
    "GetStaticMethodID";
    "CallStaticObjectMethod";
    "CallStaticObjectMethodV";
    "CallStaticObjectMethodA";
    "CallStaticBooleanMethod";
    "CallStaticBooleanMethodV";
    "CallStaticBooleanMethodA";
    "CallStaticByteMethod";
    "CallStaticByteMethodV";
    "CallStaticByteMethodA";
    "CallStaticCharMethod";
    "CallStaticCharMethodV";
    "CallStaticCharMethodA";
    "CallStaticShortMethod";
    "CallStaticShortMethodV";
    "CallStaticShortMethodA";
    "CallStaticIntMethod";
    "CallStaticIntMethodV";
    "CallStaticIntMethodA";
    "CallStaticLongMethod";
    "CallStaticLongMethodV";
    "CallStaticLongMethodA";
    "CallStaticFloatMethod";
    "CallStaticFloatMethodV";
    "CallStaticFloatMethodA";
    "CallStaticDoubleMethod";
    "CallStaticDoubleMethodV";
    "CallStaticDoubleMethodA";
    "CallStaticVoidMethod";
    "CallStaticVoidMethodV";
    "CallStaticVoidMethodA";
    "GetStaticFieldID";
    "GetStaticObjectField";
    "GetStaticBooleanField";
    "GetStaticByteField";
    "GetStaticCharField";
    "GetStaticShortField";
    "GetStaticIntField";
    "GetStaticLongField";
    "GetStaticFloatField";
    "GetStaticDoubleField";
    "SetStaticObjectField";
    "SetStaticBooleanField";
    "SetStaticByteField";
    "SetStaticCharField";
    "SetStaticShortField";
    "SetStaticIntField";
    "SetStaticLongField";
    "SetStaticFloatField";
    "SetStaticDoubleField";
    "NewString";
    "GetStringLength";
    "GetStringChars";
    "ReleaseStringChars";
    "NewStringUTF";
    "GetStringUTFLength";
    "GetStringUTFChars";
    "ReleaseStringUTFChars";
    "GetArrayLength";
    "NewObjectArray";
    "GetObjectArrayElement";
    "SetObjectArrayElement";
    "NewBooleanArray";
    "NewByteArray";
    "NewCharArray";
    "NewShortArray";
    "NewIntArray";
    "NewLongArray";
    "NewFloatArray";
    "NewDoubleArray";
    "GetBooleanArrayElements";
    "GetByteArrayElements";
    "GetCharArrayElements";
    "GetShortArrayElements";
    "GetIntArrayElements";
    "GetLongArrayElements";
    "GetFloatArrayElements";
    "GetDoubleArrayElements";
    "ReleaseBooleanArrayElements";
    "ReleaseByteArrayElements";
    "ReleaseCharArrayElements";
    "ReleaseShortArrayElements";
    "ReleaseIntArrayElements";
    "ReleaseLongArrayElements";
    "ReleaseFloatArrayElements";
    "ReleaseDoubleArrayElements";
    "GetBooleanArrayRegion";
    "GetByteArrayRegion";
    "GetCharArrayRegion";
    "GetShortArrayRegion";
    "GetIntArrayRegion";
    "GetLongArrayRegion";
    "GetFloatArrayRegion";
    "GetDoubleArrayRegion";
    "SetBooleanArrayRegion";
    "SetByteArrayRegion";
    "SetCharArrayRegion";
    "SetShortArrayRegion";
    "SetIntArrayRegion";
    "SetLongArrayRegion";
    "SetFloatArrayRegion";
    "SetDoubleArrayRegion";
    "RegisterNatives";
    "UnregisterNatives";
    "MonitorEnter";
    "MonitorExit";
    "GetJavaVM";
    "GetStringRegion";
    "GetStringUTFRegion";
    "GetPrimitiveArrayCritical";
    "ReleasePrimitiveArrayCritical";
    "GetStringCritical";
    "ReleaseStringCritical";
    "NewWeakGlobalRef";
    "DeleteWeakGlobalRef";
    "ExceptionCheck";
    "NewDirectByteBuffer";
    "GetDirectBufferAddress";
    "GetDirectBufferCapacity";
    "GetObjectRefType";
  |]

let name_of_index index =
  if index >= 0 && index < Array.length names then names.(index)
  else sprintf "JNIEnv[%d]" index

let fresh_identity t =
  let id = Internal t.next_identity in
  t.next_identity <- t.next_identity + 1;
  id

let resolve t handle =
  Option.value (Hashtbl.find t.sources handle) ~default:(External handle)

let intern_identity t kind id =
  match id with
  | External 0L -> 0L
  | _ -> (
      match Hashtbl.find t.handles (kind, id) with
      | Some handle -> handle
      | None ->
          let handle = t.next_handle in
          t.next_handle <- Int64.(handle + 0x10L);
          Hashtbl.set t.handles ~key:(kind, id) ~data:handle;
          Hashtbl.set t.sources ~key:handle ~data:id;
          handle)

let intern ?(global = false) t id =
  intern_identity t (if global then Global else Local) (External id)

let identity t handle =
  match Hashtbl.find t.sources handle with
  | Some (External id) -> Some id
  | _ -> None

let rec class_identity t name =
  match Hashtbl.find t.classes name with
  | Some id -> id
  | None ->
      let id = fresh_identity t in
      Hashtbl.set t.classes ~key:name ~data:id;
      Hashtbl.set t.class_names ~key:id ~data:name;
      id

and register_class t (decl : class_decl) =
  let id = class_identity t decl.name in
  let register_methods static methods =
    List.iter methods ~f:(fun method_decl ->
        let method_id = fresh_identity t in
        Hashtbl.set t.methods ~key:method_id
          ~data:{ method_decl; owner = id; static };
        Hashtbl.set t.method_ids
          ~key:(id, method_decl.name, method_decl.signature, static)
          ~data:method_id)
  in
  register_methods false decl.methods;
  register_methods true decl.static_methods;
  let register_fields static fields =
    List.iter fields ~f:(fun field_decl ->
        let field_id = fresh_identity t in
        Hashtbl.set t.fields ~key:field_id
          ~data:{ field_decl; owner = id; static };
        Hashtbl.set t.field_ids
          ~key:(id, field_decl.name, field_decl.signature, static)
          ~data:field_id)
  in
  register_fields false decl.fields;
  register_fields true decl.static_fields

let create ?(first_handle = 0x52030000L) ?read_string ?alloc_string
    ?(class_of = fun _ -> None) ?(default = fun _ _ -> Value 0L)
    ?(version = 0x10006L) ?log ?(classes = []) ?(objects = []) () =
  let t =
    {
      next_handle = first_handle;
      next_identity = 0;
      handles = Hashtbl.Poly.create ();
      sources = Hashtbl.Poly.create ();
      classes = Hashtbl.Poly.create ();
      class_names = Hashtbl.Poly.create ();
      object_classes = Hashtbl.Poly.create ();
      arrays = Hashtbl.Poly.create ();
      methods = Hashtbl.Poly.create ();
      method_ids = Hashtbl.Poly.create ();
      fields = Hashtbl.Poly.create ();
      field_ids = Hashtbl.Poly.create ();
      strings = Hashtbl.Poly.create ();
      strings_by_content = Hashtbl.Poly.create ();
      read_string;
      alloc_string;
      class_of;
      default;
      version;
      log;
      env = 0L;
      vm = 0L;
    }
  in
  List.iter classes ~f:(register_class t);
  List.iter objects ~f:(fun obj ->
      let class_id = class_identity t obj.class_name in
      Hashtbl.set t.object_classes ~key:(External obj.identity) ~data:class_id;
      Hashtbl.set t.arrays ~key:(External obj.identity) ~data:obj.elements);
  t

let read_string t address =
  Option.map t.read_string ~f:(fun read -> read address)

let string_identity ?(fresh = false) t content =
  let reuse =
    if fresh then None else Hashtbl.find t.strings_by_content content
  in
  match reuse with
  | Some id -> id
  | None ->
      let id = fresh_identity t in
      Hashtbl.set t.strings ~key:id ~data:{ content; address = None };
      if not fresh then Hashtbl.set t.strings_by_content ~key:content ~data:id;
      id

let rec answer t = function
  | Value value -> value
  | Object id -> intern t id
  | String content -> intern_identity t Local (string_identity t content)
  | Handle handle -> handle
  | Fresh -> intern_identity t Local (fresh_identity t)

let method_id t ~static class_handle name signature =
  let owner = resolve t class_handle in
  Option.map
    (Hashtbl.find t.method_ids (owner, name, signature, static))
    ~f:(intern_identity t Local)

let field_id t ~static class_handle name signature =
  let owner = resolve t class_handle in
  Option.map
    (Hashtbl.find t.field_ids (owner, name, signature, static))
    ~f:(intern_identity t Local)

let call_method (t : t) call ~static method_handle =
  match Hashtbl.find t.methods (resolve t method_handle) with
  | Some info when Bool.equal info.static static ->
      answer t (info.method_decl.answer t call)
  | Some _ | None -> answer t (t.default t call)

let get_field (t : t) call ~static field_handle =
  match Hashtbl.find t.fields (resolve t field_handle) with
  | Some info when Bool.equal info.static static ->
      answer t info.field_decl.value
  | Some _ | None -> answer t (t.default t call)

let get_object_class t object_handle =
  let object_id = resolve t object_handle in
  let class_id =
    match Hashtbl.find t.object_classes object_id with
    | Some id -> id
    | None -> (
        let declared =
          match object_id with
          | External id -> t.class_of id
          | Internal _ -> Hashtbl.find t.class_names object_id
        in
        match declared with
        | Some name -> class_identity t name
        | None ->
            let id = fresh_identity t in
            Hashtbl.set t.object_classes ~key:object_id ~data:id;
            id)
  in
  intern_identity t Local class_id

let string_address t id =
  match Hashtbl.find t.strings id with
  | None -> 0L
  | Some info -> (
      match info.address with
      | Some address -> address
      | None -> (
          match t.alloc_string with
          | None -> invalid_arg "Bap_emu.Jni: no alloc_string callback"
          | Some alloc ->
              let address = alloc info.content in
              info.address <- Some address;
              address))

let detail2 name signature = Some (sprintf "%s %s" name signature)

let compute t call =
  let index = call.index in
  match index with
  | 4 -> (t.version, None)
  | 6 ->
      let name = Option.value (read_string t (arg call 1)) ~default:"" in
      (intern_identity t Local (class_identity t name), Some name)
  | 21 -> (intern_identity t Global (resolve t (arg call 1)), None)
  | 22 | 23 | 166 | 170 | 227 -> (0L, None)
  | 24 ->
      let same =
        if Int64.equal (arg call 1) 0L || Int64.equal (arg call 2) 0L then
          Int64.equal (arg call 1) (arg call 2)
        else Poly.equal (resolve t (arg call 1)) (resolve t (arg call 2))
      in
      ((if same then 1L else 0L), None)
  | 25 -> (intern_identity t Local (resolve t (arg call 1)), None)
  | 28 | 29 | 30 -> (call_method t call ~static:false (arg call 2), None)
  | 31 -> (get_object_class t (arg call 1), None)
  | 33 | 113 ->
      let static = index = 113 in
      let name = Option.value (read_string t (arg call 2)) ~default:"" in
      let signature = Option.value (read_string t (arg call 3)) ~default:"" in
      let result =
        match method_id t ~static (arg call 1) name signature with
        | Some id -> id
        | None -> answer t (t.default t call)
      in
      (result, detail2 name signature)
  | 94 | 144 ->
      let static = index = 144 in
      let name = Option.value (read_string t (arg call 2)) ~default:"" in
      let signature = Option.value (read_string t (arg call 3)) ~default:"" in
      let result =
        match field_id t ~static (arg call 1) name signature with
        | Some id -> id
        | None -> answer t (t.default t call)
      in
      (result, detail2 name signature)
  | _ when index >= 34 && index <= 63 ->
      (call_method t call ~static:false (arg call 2), None)
  | _ when index >= 64 && index <= 93 ->
      (call_method t call ~static:false (arg call 3), None)
  | _ when index >= 95 && index <= 103 ->
      (get_field t call ~static:false (arg call 2), None)
  | _ when index >= 114 && index <= 143 ->
      (call_method t call ~static:true (arg call 2), None)
  | _ when index >= 145 && index <= 153 ->
      (get_field t call ~static:true (arg call 2), None)
  | 167 ->
      let content = Option.value (read_string t (arg call 1)) ~default:"" in
      ( intern_identity t Local (string_identity ~fresh:true t content),
        Some content )
  | 164 | 168 -> (
      match Hashtbl.find t.strings (resolve t (arg call 1)) with
      | Some info -> (Int64.of_int (String.length info.content), None)
      | None -> (answer t (t.default t call), None))
  | 165 | 169 -> (string_address t (resolve t (arg call 1)), None)
  | 171 -> (
      match Hashtbl.find t.arrays (resolve t (arg call 1)) with
      | Some elements -> (Int64.of_int (List.length elements), None)
      | None -> (answer t (t.default t call), None))
  | 172 ->
      let length = Int64.to_int_exn (arg call 1) in
      if length < 0 || length > 1_000_000 then
        invalid_arg "Bap_emu.Jni: unreasonable object-array length";
      let id = fresh_identity t in
      let initial = Handle (arg call 3) in
      Hashtbl.set t.arrays ~key:id
        ~data:(List.init length ~f:(fun _ -> initial));
      (intern_identity t Local id, None)
  | 173 -> (
      match Hashtbl.find t.arrays (resolve t (arg call 1)) with
      | Some elements -> (
          match List.nth elements (Int64.to_int_exn (arg call 2)) with
          | Some value -> (answer t value, None)
          | None -> (answer t (t.default t call), None))
      | None -> (answer t (t.default t call), None))
  | 219 -> (0L, Some (sprintf "vm-out=%Lx" (arg call 1)))
  | 226 -> (intern_identity t Weak (resolve t (arg call 1)), None)
  | _ -> (answer t (t.default t call), None)

let dispatch (t : t) (call : call) =
  let result, detail = compute t call in
  Option.iter t.log ~f:(fun log ->
      log
        ({ call; name = name_of_index call.index; detail; result }
          : call_record));
  result

module type Emulator = sig
  type t

  val read : t -> int64 -> int -> string
  val write : t -> int64 -> string -> unit
  val reg : t -> string -> int64
  val set_reg : t -> string -> int64 -> unit
  val set_pc : t -> int64 -> unit
end

type layout = {
  vm : int64;
  vm_functions : int64;
  env : int64;
  env_functions : int64;
  env_stubs : int64;
  env_dispatcher : int64;
  vm_stubs : int64;
  vm_dispatcher : int64;
}

module Make (E : Emulator) = struct
  let word value =
    let bytes = Stdlib.Bytes.create 8 in
    Stdlib.Bytes.set_int64_le bytes 0 value;
    Stdlib.Bytes.to_string bytes

  let write_word emu address value = E.write emu address (word value)

  let read_string emu address =
    if Int64.(address < 0x10000L) then ""
    else
      let buffer = Buffer.create 32 in
      let rec loop offset =
        if offset < 4096 then
          match E.read emu Int64.(address + of_int offset) 1 with
          | "\000" -> ()
          | char ->
              Buffer.add_string buffer char;
              loop (offset + 1)
      in
      loop 0;
      Buffer.contents buffer

  let write_stubs emu ~stubs ~dispatcher count =
    for index = 0 to count - 1 do
      let at = Int64.(stubs + of_int Int.(index * 8)) in
      let branch = Int64.(dispatcher - (at + 4L)) in
      if
        Int64.(branch % 4L <> 0L || branch < -0x8000000L || branch > 0x7fffffcL)
      then
        invalid_arg
          "Bap_emu.Jni: dispatcher is outside the AArch64 branch range";
      let movz =
        Int32.(0x52800008l lor shift_left (Int32.of_int_exn index) 5)
      in
      let offset = Int64.to_int32_trunc Int64.(branch / 4L) in
      let branch = Int32.(0x14000000l lor (offset land 0x03ffffffl)) in
      let bytes = Stdlib.Bytes.create 8 in
      Stdlib.Bytes.set_int32_le bytes 0 movz;
      Stdlib.Bytes.set_int32_le bytes 4 branch;
      E.write emu at (Stdlib.Bytes.to_string bytes)
    done

  let install (t : t) emu (layout : layout) =
    t.env <- layout.env;
    t.vm <- layout.vm;
    write_word emu layout.vm layout.vm_functions;
    write_word emu layout.env layout.env_functions;
    write_stubs emu ~stubs:layout.env_stubs ~dispatcher:layout.env_dispatcher
      233;
    write_stubs emu ~stubs:layout.vm_stubs ~dispatcher:layout.vm_dispatcher 8;
    for index = 0 to 232 do
      write_word emu
        Int64.(layout.env_functions + of_int Int.(index * 8))
        Int64.(layout.env_stubs + of_int Int.(index * 8))
    done;
    for index = 0 to 7 do
      write_word emu
        Int64.(layout.vm_functions + of_int Int.(index * 8))
        Int64.(layout.vm_stubs + of_int Int.(index * 8))
    done

  let args emu = Array.init 8 ~f:(fun n -> E.reg emu (sprintf "X%d" n))

  let serve (t : t) emu =
    let call : call =
      { index = Int64.to_int_exn (E.reg emu "X8"); args = args emu }
    in
    if call.index = 219 then write_word emu (arg call 1) t.vm;
    let result = dispatch t call in
    E.set_reg emu "X0" result;
    E.set_pc emu (E.reg emu "X30")

  let serve_vm (t : t) emu =
    let index = Int64.to_int_exn (E.reg emu "X8") in
    let result =
      match index with
      | 6 ->
          let requested = E.reg emu "X2" in
          if Int64.equal requested t.version then (
            write_word emu (E.reg emu "X1") t.env;
            0L)
          else -2L
      | _ -> 0L
    in
    Option.iter t.log ~f:(fun log ->
        log
          {
            call = { index; args = args emu };
            name =
              (if index = 6 then "JavaVM.GetEnv" else sprintf "JavaVM[%d]" index);
            detail = None;
            result;
          });
    E.set_reg emu "X0" result;
    E.set_pc emu (E.reg emu "X30")
end
