open Core
open Regular.Std
module Filename = Stdlib.Filename
module Sys = Stdlib.Sys
module Unix = Caml_unix

let ( / ) = Filename.concat

(* Windows doesn't rename a file onto a read-only one, so the cache files
   are writable there *)
let make_read_only file = if not Sys.win32 then Unix.chmod file 0o444

let write_to_file ?temp_dir writer file data =
  let temp_dir = Option.value ~default:(Filename.dirname file) temp_dir in
  let tmp, ch = Filename.open_temp_file ~temp_dir "tmp" "" in
  protect
    ~f:(fun () -> Data.Write.to_channel writer ch data)
    ~finally:(fun () ->
      Out_channel.close ch;
      make_read_only tmp;
      Sys.rename tmp file)

let open_temp temp_dir =
  let tmp = Filename.temp_file ~temp_dir "tmp" "index" in
  try (tmp, Unix.(openfile tmp [ O_RDWR ] 0o600))
  with e ->
    Sys.remove tmp;
    raise e

(* Windows keeps a mapped file locked until the mapping is collected, so
   there the cache files, which the cache renames, removes, and
   overwrites, are read and written without mapping them *)
let binable_to_file_unmapped ?temp_dir b file data =
  let temp_dir = Option.value ~default:(Filename.dirname file) temp_dir in
  let tmp, ch =
    Filename.open_temp_file ~mode:[ Open_binary ] ~temp_dir "tmp" ""
  in
  protect
    ~f:(fun () -> Out_channel.output_string ch (Binable.to_string b data))
    ~finally:(fun () ->
      Out_channel.close ch;
      Sys.rename tmp file)

let binable_to_file : type t.
    ?temp_dir:string ->
    (module Binable.S with type t = t) ->
    string ->
    t ->
    unit =
 fun ?temp_dir b file data ->
  if Sys.win32 then binable_to_file_unmapped ?temp_dir b file data
  else
  let module T = (val b) in
  let temp_dir = Option.value ~default:(Filename.dirname file) temp_dir in
  let tmp, fd = open_temp temp_dir in
  let size = T.bin_size_t data in
  protect
    ~f:(fun () ->
      let buf =
        Mmap.V1.map_file fd Bigarray.char Bigarray.c_layout true [| size |]
      in
      ignore @@ T.bin_write_t (Bigarray.array1_of_genarray buf) ~pos:0 data)
    ~finally:(fun () ->
      Unix.close fd;
      make_read_only tmp;
      Sys.rename tmp file)

let binable_from_file : type t.
    (module Binable.S with type t = t) -> string -> t =
 fun b file ->
  if Sys.win32 then Binable.of_string b (In_channel.read_all file)
  else
  let module T = (val b) in
  let fd = Unix.(openfile file [ O_RDONLY ] 0o400) in
  let data =
    Mmap.V1.map_file fd Bigarray.char Bigarray.c_layout false [| -1 |]
  in
  let pos_ref = ref 0 in
  T.bin_read_t (Bigarray.array1_of_genarray data) ~pos_ref

let read_from_file reader file =
  In_channel.with_file file ~f:(Data.Read.of_channel reader)
