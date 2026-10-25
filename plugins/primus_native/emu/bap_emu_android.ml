open Core

type parcel = {
  identity : int64;
  data : Buffer.t;
  mutable cursor : int;
  mutable exception_code : int32;
}

type service = {
  name : string;
  identity : int64;
  class_name : string;
  transact : int64 -> parcel -> parcel -> unit;
}

type t = {
  mutable next_identity : int64;
  services : service String.Table.t;
  by_identity : service Int64.Table.t;
  parcels : parcel Int64.Table.t;
  classes : string Int64.Table.t;
}

let create ?(first_identity = 0x60000000L) ?(services = []) () =
  let t =
    {
      next_identity = first_identity;
      services = String.Table.create ();
      by_identity = Int64.Table.create ();
      parcels = Int64.Table.create ();
      classes = Int64.Table.create ();
    }
  in
  let add service =
    if Hashtbl.mem t.services service.name then
      invalid_argf "Bap_emu.Android: duplicate service %s" service.name ();
    if Hashtbl.mem t.by_identity service.identity then
      invalid_argf "Bap_emu.Android: duplicate identity %Lx" service.identity ();
    Hashtbl.set t.services ~key:service.name ~data:service;
    Hashtbl.set t.by_identity ~key:service.identity ~data:service;
    Hashtbl.set t.classes ~key:service.identity ~data:service.class_name
  in
  List.iter services ~f:add;
  t

let add_service t service =
  if Hashtbl.mem t.services service.name then
    invalid_argf "Bap_emu.Android: duplicate service %s" service.name ();
  if Hashtbl.mem t.by_identity service.identity then
    invalid_argf "Bap_emu.Android: duplicate identity %Lx" service.identity ();
  Hashtbl.set t.services ~key:service.name ~data:service;
  Hashtbl.set t.by_identity ~key:service.identity ~data:service;
  Hashtbl.set t.classes ~key:service.identity ~data:service.class_name

let find_service t name =
  Option.map (Hashtbl.find t.services name) ~f:(fun service -> service.identity)

let fresh_identity t =
  let identity = t.next_identity in
  t.next_identity <- Int64.(identity + 0x10L);
  identity

let obtain t =
  let identity = fresh_identity t in
  let parcel =
    { identity; data = Buffer.create 32; cursor = 0; exception_code = 0l }
  in
  Hashtbl.set t.parcels ~key:identity ~data:parcel;
  Hashtbl.set t.classes ~key:identity ~data:"android/os/Parcel";
  parcel

let find_parcel t identity = Hashtbl.find t.parcels identity
let parcel_identity (parcel : parcel) = parcel.identity

let write_int parcel value =
  for index = 0 to 3 do
    let byte =
      Stdlib.Int32.logand
        (Stdlib.Int32.shift_right_logical value (index * 8))
        0xffl
      |> Stdlib.Int32.to_int
    in
    Buffer.add_char parcel.data (Char.of_int_exn byte)
  done

let write_interface_token parcel token =
  write_int parcel (Int32.of_int_exn (String.length token));
  Buffer.add_string parcel.data token

let read_int parcel =
  if parcel.cursor + 4 > Buffer.length parcel.data then None
  else
    let bytes = Buffer.contents parcel.data in
    let value =
      List.init 4 ~f:(fun index ->
          Stdlib.Int32.shift_left
            (Stdlib.Int32.of_int (Char.to_int bytes.[parcel.cursor + index]))
            (index * 8))
      |> List.fold ~init:0l ~f:Stdlib.Int32.logor
    in
    parcel.cursor <- parcel.cursor + 4;
    Some value

let read_interface_token parcel =
  match read_int parcel with
  | None -> None
  | Some length ->
      let length = Int32.to_int_exn length in
      if length < 0 || parcel.cursor + length > Buffer.length parcel.data then
        None
      else
        let token =
          String.sub
            (Buffer.contents parcel.data)
            ~pos:parcel.cursor ~len:length
        in
        parcel.cursor <- parcel.cursor + length;
        Some token

let set_exception parcel code = parcel.exception_code <- code
let read_exception parcel = parcel.exception_code

let transact t identity code request reply =
  match Hashtbl.find t.by_identity identity with
  | None ->
      reply.exception_code <- -1l;
      -1L
  | Some service ->
      service.transact code request reply;
      0L

let class_of t identity = Hashtbl.find t.classes identity

let method_arg (call : Bap_emu_jni.call) index =
  let base = if call.index >= 64 && call.index <= 93 then 4 else 3 in
  let index = base + index in
  if index < Array.length call.args then call.args.(index) else 0L

let parcel_of_handle t jni handle =
  match Bap_emu_jni.identity jni handle with
  | None -> None
  | Some identity -> Hashtbl.find t.parcels identity

let jni_classes t =
  let methodDecl name signature answer : Bap_emu_jni.method_decl =
    { name; signature; answer }
  in
  let empty name =
    {
      Bap_emu_jni.name;
      methods = [];
      static_methods = [];
      fields = [];
      static_fields = [];
    }
  in
  let service_manager =
    let get_service jni call =
      match Bap_emu_jni.string_value jni (method_arg call 0) with
      | None -> Bap_emu_jni.Value 0L
      | Some name -> (
          match find_service t name with
          | Some identity -> Bap_emu_jni.Object identity
          | None -> Bap_emu_jni.Value 0L)
    in
    {
      (empty "android/os/ServiceManager") with
      static_methods =
        [
          methodDecl "getService" "(Ljava/lang/String;)Landroid/os/IBinder;"
            get_service;
        ];
    }
  in
  let parcel_class =
    let obtain _ _ = Bap_emu_jni.Object (obtain t).identity in
    let write_token jni (call : Bap_emu_jni.call) =
      match
        ( parcel_of_handle t jni call.args.(1),
          Bap_emu_jni.string_value jni (method_arg call 0) )
      with
      | Some parcel, Some token ->
          write_interface_token parcel token;
          Bap_emu_jni.Value 0L
      | _ -> Bap_emu_jni.Value 0L
    in
    let write_integer jni (call : Bap_emu_jni.call) =
      match parcel_of_handle t jni call.args.(1) with
      | Some parcel ->
          write_int parcel (Int64.to_int32_trunc (method_arg call 0));
          Bap_emu_jni.Value 0L
      | None -> Bap_emu_jni.Value 0L
    in
    let read_exception jni (call : Bap_emu_jni.call) =
      match parcel_of_handle t jni call.args.(1) with
      | Some parcel -> Bap_emu_jni.Value (Int64.of_int32 parcel.exception_code)
      | None -> Bap_emu_jni.Value 0L
    in
    {
      (empty "android/os/Parcel") with
      static_methods = [ methodDecl "obtain" "()Landroid/os/Parcel;" obtain ];
      methods =
        [
          methodDecl "writeInterfaceToken" "(Ljava/lang/String;)V" write_token;
          methodDecl "writeInt" "(I)V" write_integer;
          methodDecl "readException" "()V" read_exception;
        ];
    }
  in
  let binder =
    let transact_method jni (call : Bap_emu_jni.call) =
      let binder =
        Option.value (Bap_emu_jni.identity jni call.args.(1)) ~default:0L
      in
      match
        ( parcel_of_handle t jni (method_arg call 1),
          parcel_of_handle t jni (method_arg call 2) )
      with
      | Some request, Some reply ->
          let result = transact t binder (method_arg call 0) request reply in
          Bap_emu_jni.Value (if Int64.equal result 0L then 1L else 0L)
      | _ -> Bap_emu_jni.Value 0L
    in
    {
      (empty "android/os/IBinder") with
      methods =
        [
          methodDecl "transact" "(ILandroid/os/Parcel;Landroid/os/Parcel;I)Z"
            transact_method;
        ];
    }
  in
  [ service_manager; parcel_class; binder ]

module Saved_state = struct
  type parcel_state = {
    identity : int64;
    data : string;
    cursor : int;
    exception_code : int32;
  }
  [@@deriving bin_io]

  type service_state = { name : string; identity : int64; class_name : string }
  [@@deriving bin_io]

  type t = {
    format : int;
    next_identity : int64;
    services : service_state list;
    classes : (int64 * string) list;
    parcels : parcel_state list;
  }
  [@@deriving bin_io]
end

let export_state t =
  let services =
    Hashtbl.data t.services
    |> List.map ~f:(fun service ->
        {
          Saved_state.name = service.name;
          identity = service.identity;
          class_name = service.class_name;
        })
  in
  let parcels =
    Hashtbl.data t.parcels
    |> List.map ~f:(fun (parcel : parcel) ->
        {
          Saved_state.identity = parcel.identity;
          data = Buffer.contents parcel.data;
          cursor = parcel.cursor;
          exception_code = parcel.exception_code;
        })
  in
  Binable.to_string
    (module Saved_state)
    {
      format = 1;
      next_identity = t.next_identity;
      services;
      classes = Hashtbl.to_alist t.classes;
      parcels;
    }

let import_state t data =
  let invalid () = invalid_arg "Bap_emu.Android: invalid saved state" in
  let (state : Saved_state.t) =
    match Binable.of_string (module Saved_state) data with
    | exception _ -> invalid ()
    | state -> state
  in
  if state.format <> 1 then invalid ();
  let unique_int64 values =
    let seen = Int64.Hash_set.create () in
    List.iter values ~f:(fun value ->
        if Hash_set.mem seen value then invalid ();
        Hash_set.add seen value)
  in
  unique_int64 (List.map state.services ~f:(fun service -> service.identity));
  unique_int64 (List.map state.parcels ~f:(fun parcel -> parcel.identity));
  unique_int64 (List.map state.classes ~f:fst);
  let names = String.Hash_set.create () in
  List.iter state.services ~f:(fun service ->
      if Hash_set.mem names service.name then invalid ();
      Hash_set.add names service.name;
      match Hashtbl.find t.by_identity service.identity with
      | Some current
        when String.equal current.name service.name
             && String.equal current.class_name service.class_name ->
          ()
      | _ -> invalid ());
  let parcels =
    List.map state.parcels ~f:(fun saved ->
        if saved.cursor < 0 || saved.cursor > String.length saved.data then
          invalid ();
        let parcel =
          {
            identity = saved.identity;
            data = Buffer.create (String.length saved.data);
            cursor = saved.cursor;
            exception_code = saved.exception_code;
          }
        in
        Buffer.add_string parcel.data saved.data;
        parcel)
  in
  t.next_identity <- state.next_identity;
  Hashtbl.clear t.classes;
  List.iter state.classes ~f:(fun (identity, name) ->
      Hashtbl.set t.classes ~key:identity ~data:name);
  Hashtbl.clear t.parcels;
  List.iter parcels ~f:(fun parcel ->
      Hashtbl.set t.parcels ~key:parcel.identity ~data:parcel)
