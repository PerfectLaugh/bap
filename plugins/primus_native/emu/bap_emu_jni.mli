(** A concrete model of the Java Native Interface for emulated programs.

    A target declares its classes and answers. The model owns JNI handle
    identities, method and field identifiers, strings, and call logging:
    {[
    let jni =
      Emu.Jni.create ~read_string:(read_c_string emu)
        ~alloc_string:(allocate_c_string emu)
        ~classes:
          [
            {
              Emu.Jni.name = "android/content/pm/ApplicationInfo";
              methods = [];
              static_methods = [];
              fields =
                [
                  {
                    Emu.Jni.name = "packageName";
                    signature = "Ljava/lang/String;";
                    value = Emu.Jni.String "com.example.app";
                  };
                ];
              static_fields = [];
            };
          ]
        ~log:(fun call ->
          printf "JNI %s -> %Lx (%s)\n" call.name call.result
            (Option.value call.detail ~default:""))
        ()
    in
    Emu.Jni.install jni emu layout;
    (* At the common dispatcher pause: *)
    Emu.Jni.serve jni emu
    ]}

    Object identities are stable and independent of handles. In particular,
    [GetObjectClass] and [NewGlobalRef] cache their handles, and [IsSameObject]
    compares the objects to which handles refer, not the handle values. *)

open Core

type t
(** the state of a JNI model *)

type object_id = int64
(** an identity chosen by the target for a native-side Java object *)

type call = { index : int; args : int64 array }
(** a JNI function-table index and its arguments, including [JNIEnv *] *)

type answer =
  | Value of int64  (** a scalar return value *)
  | Object of object_id  (** a handle to this object *)
  | String of string  (** a Java string with this UTF-8 content *)
  | Handle of int64  (** an existing handle, preserving its modeled identity *)
  | Fresh  (** a fresh object with a fresh identity *)

type handler = t -> call -> answer
(** computes the answer to a method call or an unmodelled table index *)

type method_decl = { name : string; signature : string; answer : handler }
type field_decl = { name : string; signature : string; value : answer }

type class_decl = {
  name : string;
  methods : method_decl list;
  static_methods : method_decl list;
  fields : field_decl list;
  static_fields : field_decl list;
}

type object_decl = {
  identity : object_id;
  class_name : string;
  elements : answer list;  (** elements, for an object array *)
}

type call_record = {
  call : call;
  name : string;
  detail : string option;
  result : int64;
}
(** a completed call, passed to the logger after its answer is computed *)

val create :
  ?first_handle:int64 ->
  ?read_string:(int64 -> string) ->
  ?alloc_string:(string -> int64) ->
  ?class_of:(object_id -> string option) ->
  ?default:handler ->
  ?version:int64 ->
  ?versions:int64 list ->
  ?log:(call_record -> unit) ->
  ?classes:class_decl list ->
  ?objects:object_decl list ->
  unit ->
  t
(** [create ()] constructs a model. [read_string] reads a NUL-terminated
    modified-UTF-8 string from the program. [alloc_string] stores such a string
    and returns its address; it is needed by [GetStringChars] and
    [GetStringUTFChars]. [class_of] supplies the class name of an object not in
    [objects]. [default] answers calls without a built-in or declared answer and
    returns [Value 0L] by default. [version] is the JNI version that
    [GetVersion] returns, [0x10006] by default, and [versions] are the versions
    that [GetEnv] accepts, by default only [version]. [first_handle] is
    [0x52030000] by default; handles increase by 16 and are never reused. *)

val export_state : t -> string
(** [export_state jni] serializes the dynamic state of [jni], including its
    handles, object and class identities, method and field IDs, arrays, strings,
    and allocator counters. String arguments are stored by value, not as native
    pointers. Use with [Bap_emu.Checkpoint.register] to keep the state with the
    guest checkpoint. *)

val import_state : t -> string -> unit
(** [import_state jni data] replaces the dynamic state of [jni] with the state
    that {!export_state} saved. Construct [jni] with the same declarations and
    callbacks as the saved model before importing. The declarations and
    callbacks themselves are not serialized. Raises [Invalid_argument], if
    [data] is not a valid JNI model state. *)

val intern : ?global:bool -> t -> object_id -> int64
(** [intern t id] returns the stable local handle of [id], or its stable global
    handle with [~global:true]. Null maps to null. *)

val identity : t -> int64 -> object_id option
(** [identity t handle] resolves a model-created handle to its object identity.
    Class, method, field, string, and synthesized identities return [None]. *)

val dispatch : t -> call -> int64
(** [dispatch t call] answers a JNI call and logs it. *)

val name_of_index : int -> string
(** the standard JNI function name, or ["JNIEnv[index]"] for an unknown index *)

module type Emulator = sig
  type t

  val read : t -> int64 -> int -> string
  val write : t -> int64 -> string -> unit
  val reg : t -> string -> int64
  val set_reg : t -> string -> int64 -> unit
  val set_pc : t -> int64 -> unit
end

type layout = {
  vm : int64;  (** the JavaVM object, whose first word is [vm_functions] *)
  vm_functions : int64;
  env : int64;  (** the JNIEnv object, whose first word is [env_functions] *)
  env_functions : int64;
  env_stubs : int64;  (** room for 233 eight-byte AArch64 stubs *)
  env_dispatcher : int64;
  vm_stubs : int64;  (** room for eight eight-byte AArch64 stubs *)
  vm_dispatcher : int64;
}
(** addresses of the modeled objects, tables, and code, in already-mapped
    writable memory. Each dispatcher must be within the AArch64 branch range of
    its stubs. *)

module Make (E : Emulator) : sig
  val install : t -> E.t -> layout -> unit
  (** [install jni emu layout] writes the modeled objects, function tables, and
      AArch64 stubs. JNIEnv entries call [env_dispatcher] with the table index
      in [W8]. JavaVM entries likewise call [vm_dispatcher]. *)

  val serve : t -> E.t -> unit
  (** [serve jni emu] serves a pause at [env_dispatcher], reading [X0] through
      [X7], returning the answer in [X0], and continuing at [X30]. *)

  val serve_vm : t -> E.t -> unit
  (** [serve_vm jni emu] serves a pause at [vm_dispatcher]. [GetEnv] writes the
      modeled JNIEnv pointer and returns [JNI_OK], or [JNI_EVERSION] for an
      unsupported version. [AttachCurrentThread] and
      [AttachCurrentThreadAsDaemon] write the same pointer and return [JNI_OK].
  *)

  val read_string : E.t -> int64 -> string
  (** reads at most 4096 bytes, including the terminating NUL *)
end
