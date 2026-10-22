(* The cache of the Lisp programs, whose parsing and typing take most of
   the time, that a process spends to start a Primus machine, or to lift
   with the Lisp semantics.

   The entries are in the folder of the BAP_PRIMUS_LISP_CACHE variable,
   which the processes may share, while their caches are of their own,
   e.g., the cases of the testsuite, or else in the primus-lisp folder
   of the cache of BAP, and nothing is cached without either. An entry
   is a value of its representation, with bin_prot, whose shape is in
   its key, so that the entries of the other representations are not
   read, and is written whole, and renamed, so that the processes, that
   share the folder, read only the complete ones. An entry, that can't
   be read, is computed anew. The keys have the version and the build
   of the program, see [build], as its code computes the entries. *)

open Core

let variable = "BAP_PRIMUS_LISP_CACHE"

let folder () =
  match Stdlib.Sys.getenv_opt variable with
  | Some dir when not (String.is_empty dir) -> Some dir
  | _ ->
      Option.map (Bap_main.Extension.Configuration.cachedir ()) ~f:(fun dir ->
          Filename.concat dir "primus-lisp")

(* the build of the program, whose code computes the entries, e.g.,
   types the programs, by the size and the time of its executable, as
   the bap scripts do *)
let build =
  lazy
    (match Caml_unix.stat Stdlib.Sys.executable_name with
    | { st_size; st_mtime; _ } -> sprintf "%d:%f" st_size st_mtime
    | exception Caml_unix.Unix_error _ -> "")

let key (type t) (module T : Binable.S with type t = t) parts =
  Bap_main.Extension.Configuration.version :: Lazy.force build
  :: Bin_prot.Shape.eval_to_digest_string T.bin_shape_t
  :: parts
  |> String.concat ~sep:"\000" |> Stdlib.Digest.string |> Stdlib.Digest.to_hex

let file dir ~kind key = Filename.concat dir (kind ^ "-" ^ key)

let load (type t) (module T : Binable.S with type t = t) ~kind parts =
  match folder () with
  | None -> None
  | Some dir -> (
      let path = file dir ~kind (key (module T) parts) in
      try Some (Binable.of_string (module T) (In_channel.read_all path))
      with _ -> None)

let rec mkdir dir =
  if not (Stdlib.Sys.file_exists dir) then begin
    mkdir (Filename.dirname dir);
    try Stdlib.Sys.mkdir dir 0o755 with Sys_error _ -> ()
  end

(* the entries of a kind, that the other builds or the other programs
   left, are removed, but the latest [kept] ones, as the BAP cache
   doesn't collect them *)
let kept = 16

let prune dir ~kind =
  let prefix = kind ^ "-" in
  Stdlib.Sys.readdir dir |> Array.to_list
  |> List.filter_map ~f:(fun name ->
      if
        String.is_prefix name ~prefix
        && not (String.is_suffix name ~suffix:".tmp")
      then
        let path = Filename.concat dir name in
        match Caml_unix.stat path with
        | { st_mtime; _ } -> Some (st_mtime, path)
        | exception Caml_unix.Unix_error _ -> None
      else None)
  |> List.sort ~compare:(fun (x, _) (y, _) -> Float.compare y x)
  |> Fn.flip List.drop kept
  |> List.iter ~f:(fun (_, path) ->
      try Stdlib.Sys.remove path with Sys_error _ -> ())

let store (type t) (module T : Binable.S with type t = t) ~kind parts x =
  match folder () with
  | None -> ()
  | Some dir -> (
      let path = file dir ~kind (key (module T) parts) in
      try
        mkdir dir;
        let tmp, out =
          Stdlib.Filename.open_temp_file ~mode:[ Open_binary ] ~temp_dir:dir
            kind ".tmp"
        in
        try
          Exn.protect
            ~f:(fun () ->
              Out_channel.output_string out (Binable.to_string (module T) x))
            ~finally:(fun () -> Out_channel.close out);
          Stdlib.Sys.rename tmp path;
          prune dir ~kind
        with exn ->
          (try Stdlib.Sys.remove tmp with Sys_error _ -> ());
          raise exn
      with _ -> ())
