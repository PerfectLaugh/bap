open Core
open Bap_core_theory
open Bap.Std
module Sys = Stdlib.Sys
module Config = Bap_main.Extension.Configuration

let ( / ) = Filename.concat

type error =
  [ `Corrupted of string
  | `No_signatures
  | `No_entry of string
  | `Sys_error of string ]

type 'a data = { name : string; load : bytes -> 'a; save : 'a -> bytes }

exception Failed of error

let fail error = raise (Failed error)
let corrupted entry err = `Corrupted (sprintf "%s: %s" entry err)
let zip_error entry err = fail (corrupted entry err)
let compiler_name = Option.value_map ~default:"default" ~f:Theory.Compiler.name

let matches_modulo_bits t name =
  match Theory.Target.matching t name with
  | None -> false
  | Some t' -> Theory.Target.bits t = Theory.Target.bits t'

(* the archives are read and written as a whole *)
module Zip = struct
  let read file =
    match Zipc.of_binary_string (In_channel.read_all file) with
    | Ok zip -> zip
    | Error err -> zip_error file err

  let read_if_exists file =
    if Sys.file_exists file then read file else Zipc.empty

  let entries zip = List.rev (Zipc.fold List.cons zip [])

  let read_entry entry =
    match Zipc.Member.kind entry with
    | Dir -> ""
    | File file -> (
        match Zipc.File.to_binary_string file with
        | Ok data -> data
        | Error err -> zip_error (Zipc.Member.path entry) err)

  let add zip name data =
    match
      Result.bind (Zipc.File.deflate_of_binary_string data) ~f:(fun file ->
          Zipc.Member.make ~path:name (File file))
    with
    | Ok entry -> Zipc.add entry zip
    | Error err -> zip_error name err

  let write file zip =
    match Zipc.to_binary_string zip with
    | Ok data -> Out_channel.write_all file ~data
    | Error err -> zip_error file err
end

let matching_entry ?compiler target data entry =
  let filename = Zipc.Member.path entry in
  match String.split filename ~on:'/' with
  | [ p1; p2; p3 ] ->
      matches_modulo_bits target p1
      && String.equal (compiler_name compiler) p2
      && String.equal data.name p3
  | _ -> fail (`Corrupted ("invalid entry name: " ^ filename))

let read_entry ?compiler target data file =
  Zip.entries (Zip.read file)
  |> List.find ~f:(matching_entry ?compiler target data)
  |> Option.map ~f:(fun entry ->
      data.load (Bytes.of_string (Zip.read_entry entry)))

let target_name = Fn.compose KB.Name.unqualified Theory.Target.name

let make_entry ?compiler target data =
  target_name target / compiler_name compiler / data.name

let make_path root = root / "signatures" / "byteweight.zip"
let system_path = make_path Config.sysdatadir

let default_path =
  match Sys.getenv_opt "BAP_SIGFILE" with
  | Some path -> path
  | None -> make_path Config.datadir

(* the signatures installed with BAP, see plugins/byteweight/signatures *)
let installed_paths =
  List.map (Bap_common.sites "signatures") ~f:(fun dir ->
      dir / "byteweight.zip")

let default_paths = (default_path :: installed_paths) @ [ system_path ]

let try_lookup ?(paths = []) ?(defaults = true) ?compiler target data =
  (if defaults then paths @ default_paths else paths)
  |> List.find_map ~f:(fun path ->
      if Sys.file_exists path then read_entry ?compiler target data path
      else None)

let of_exn = function
  | Sys_error msg -> Error (`Sys_error msg)
  | Failed er -> Error er
  | other -> raise other

let lookup ?paths ?defaults ?compiler target data =
  match try_lookup ?paths ?defaults ?compiler target data with
  | exception exn -> of_exn exn
  | None -> Error (`No_entry (target_name target))
  | Some data -> Ok data

let update_or_fail ?compiler target data payload path =
  let zip = Zip.read_if_exists path in
  let zip =
    Zip.entries zip
    |> List.filter ~f:(matching_entry ?compiler target data)
    |> List.fold ~init:zip ~f:(fun zip entry ->
        Zipc.remove (Zipc.Member.path entry) zip)
  in
  Zip.add zip
    (make_entry ?compiler target data)
    (Bytes.to_string (data.save payload))
  |> Zip.write path

let copy input output =
  let len = 0x1000 in
  let buf = Bytes.create len in
  let rec loop () =
    let read = In_channel.input input ~buf ~pos:0 ~len in
    Out_channel.output output ~buf ~pos:0 ~len:read;
    if read = len then loop ()
  in
  loop ()

let temporary_copy file =
  let tmp, output = Stdlib.Filename.open_temp_file "byteweight" "copy" in
  In_channel.with_file file ~f:(fun input -> copy input output);
  Out_channel.close output;
  tmp

let restore ~backup path =
  match backup with
  | None -> if Sys.file_exists path then Sys.remove path
  | Some tmp ->
      In_channel.with_file tmp ~f:(fun input ->
          Out_channel.with_file path ~f:(fun output -> copy input output));
      Sys.remove tmp

let update ?compiler target data payload path =
  let backup =
    if Sys.file_exists path then Some (temporary_copy path) else None
  in
  try
    update_or_fail ?compiler target data payload path;
    Option.iter backup ~f:Sys.remove;
    Ok ()
  with exn ->
    restore ~backup path;
    of_exn exn

module Data = struct
  let registry = Hash_set.create (module String)

  let declare ~load ~save name =
    if Hash_set.mem registry name then
      failwithf
        "The byteweight data type named %S is already registered, please pick \
         another name"
        name ();
    Hash_set.add registry name;
    { load; save; name }
end

(* the old deprecated implementation *)

let resolve_path user =
  let user = Option.value_map user ~f:List.return ~default:[] in
  let paths = user @ default_paths in
  match List.find paths ~f:Sys.file_exists with
  | None -> fail `No_signatures
  | Some path -> path

let entry ?(comp = "default") ~mode arch = Arch.to_string arch / comp / mode

let load_exn ?comp ?path ~mode arch =
  let path = resolve_path path in
  let zip = try Zip.read path with Sys_error msg -> fail (`Sys_error msg) in
  let entry_path = entry ?comp ~mode arch in
  match Zipc.find entry_path zip with
  | None -> fail (`No_entry entry_path)
  | Some entry -> Ok (Stdlib.Bytes.unsafe_of_string (Zip.read_entry entry))

let load ?comp ?path ~mode arch =
  try load_exn ?comp ?path ~mode arch with Failed err -> Error err

let save_exn ?comp ~mode ~path arch data =
  try
    Zip.add (Zip.read_if_exists path) (entry ?comp ~mode arch)
      (Bytes.to_string data)
    |> Zip.write path
  with Sys_error msg -> fail (`Sys_error msg)

let save ?comp ~mode ~path arch data =
  try Ok (save_exn ?comp ~mode ~path arch data) with Failed err -> Error err

let string_of_error = function
  | `Corrupted msg -> sprintf "signature database is corrupted: %s" msg
  | `No_signatures -> "signature database doesn't exist"
  | `Sys_error msg -> sprintf "system error: %s" msg
  | `No_entry msg -> sprintf "can't access given entry: %s" msg
