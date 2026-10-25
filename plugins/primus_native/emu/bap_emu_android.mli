(** Reusable Android ServiceManager, IBinder, and Parcel models for
    {!Bap_emu_jni}. *)

open Core

type parcel
(** a stateful parcel with a stable object identity, bytes, cursor, and
    exception *)

type service = {
  name : string;
  identity : int64;
  class_name : string;
  transact : int64 -> parcel -> parcel -> unit;
}
(** a named binder service. The handler receives the transaction code, request,
    and reply; script code owns the handler. *)

type t
(** an Android environment with services and live parcels *)

val create : ?first_identity:int64 -> ?services:service list -> unit -> t
(** [create ()] constructs an empty environment. Identities increase by 16 from
    [first_identity], [0x60000000] by default. *)

val add_service : t -> service -> unit
(** registers a service under its name and identity. Raises [Invalid_argument]
    for a duplicate name or identity. *)

val find_service : t -> string -> int64 option
(** the identity of a registered service, or [None]. *)

val obtain : t -> parcel
(** a fresh parcel with the [android/os/Parcel] return class. *)

val find_parcel : t -> int64 -> parcel option
(** a live parcel by identity, including one restored from a checkpoint. *)

val parcel_identity : parcel -> int64
(** the stable external identity of a parcel. *)

val write_interface_token : parcel -> string -> unit
(** appends a length-prefixed interface token. *)

val write_int : parcel -> int32 -> unit
(** appends a little-endian 32-bit integer. *)

val read_interface_token : parcel -> string option
(** reads and advances past an interface token, if complete. *)

val read_int : parcel -> int32 option
(** reads and advances past a little-endian 32-bit integer, if complete. *)

val set_exception : parcel -> int32 -> unit
(** sets the code returned by [readException]. *)

val read_exception : parcel -> int32
(** the parcel's exception code, zero by default. *)

val transact : t -> int64 -> int64 -> parcel -> parcel -> int64
(** [transact env binder code request reply] invokes the registered binder.
    Returns zero on success and [-1] for an unknown binder, also setting the
    reply exception to [-1]. *)

val class_of : t -> int64 -> string option
(** the return class of a service or parcel identity. *)

val jni_classes : t -> Bap_emu_jni.class_decl list
(** ServiceManager.getService, Parcel.obtain/writeInterfaceToken/writeInt/
    readException, and IBinder.transact declarations for this environment. *)

val export_state : t -> string
(** serializes service metadata, return classes, live parcels, cursors,
    exceptions, and the identity cursor. Handlers are not serialized. *)

val import_state : t -> string -> unit
(** restores state saved by {!export_state}. Recreate the environment with the
    same service declarations first. Raises [Invalid_argument] for malformed
    state or missing/incompatible declarations; dynamic tables are not changed
    until validation succeeds. *)
