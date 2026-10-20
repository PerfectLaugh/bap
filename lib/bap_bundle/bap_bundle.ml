open Core
module Filename = Stdlib.Filename
module Sys = Stdlib.Sys

module Std = struct
  exception Not_a_bundle

  module Manifest = struct
    let getenv key = try Sys.getenv key with Stdlib.Not_found -> "unknown"

    type t = {
      name : string;
      version : string;
      desc : string;
      main : string;
      author : string;
      date : float;
      requires : string list;
      provides : string list;
      url : string option;
      license : string option;
      copyrights : string option;
      tags : string list;
      cons : string list;
    }
    [@@deriving bin_io, compare, fields, sexp]

    let create ?(author = getenv "USER") ?(version = "1.0.0") ?main
        ?(date = Caml_unix.time ()) ?(desc = "description not provided")
        ?(requires = []) ?(provides = []) ?url ?license ?copyrights ?(tags = [])
        ?(cons = []) name =
      {
        name;
        author;
        version;
        date;
        desc;
        requires;
        provides;
        copyrights;
        license;
        url;
        tags;
        cons;
        main = Option.value main ~default:name;
      }

    let pp_sexp ppf = function
      | Sexp.Atom _ | Sexp.List [] -> ()
      | Sexp.List (x :: xs) ->
          let open Format in
          let pp = Sexp.pp_hum_indent 1 in
          fprintf ppf "@[<v1>(%a" pp x;
          List.iter xs ~f:(fun x -> fprintf ppf "@;%a" pp x);
          fprintf ppf ")@]"

    let pp ppf m =
      let sexp = sexp_of_t m in
      Format.fprintf ppf "%a" pp_sexp sexp

    let to_string m = Format.asprintf "%a" pp m
    let of_string s = t_of_sexp (Sexp.of_string s)

    let manifest =
      let name = Filename.basename Sys.executable_name in
      ref (create name)

    let update m = manifest := m

    let switch m =
      let old = !manifest in
      manifest := m;
      old

    let current () = !manifest
  end

  type manifest = Manifest.t

  module Nameof = struct
    let manifest = "MANIFEST.scm"
  end

  module Bundle = struct
    type filename = string
    type bundle = { name : string; path : filename }
    type t = bundle

    let main =
      let name = Filename.basename Sys.executable_name in
      ref { name; path = name ^ ".bundle" }

    (* the archives are read and written as a whole *)
    module Zip = struct
      let ok_exn = function Ok x -> x | Error msg -> failwith msg

      let open_in path =
        match Zipc.of_binary_string (In_channel.read_all path) with
        | Ok zip -> zip
        | Error _ -> raise Not_a_bundle

      let entries zip = List.rev (Zipc.fold List.cons zip [])
      let filename = Zipc.Member.path

      let find_entry zip name =
        match Zipc.find name zip with
        | Some entry -> entry
        | None -> raise Stdlib.Not_found

      let read_entry entry =
        match Zipc.Member.kind entry with
        | Dir -> ""
        | File file -> ok_exn (Zipc.File.to_binary_string file)

      let add_entry ?(compress = true) zip name data =
        let file =
          if compress then Zipc.File.deflate_of_binary_string data
          else Zipc.File.stored_of_binary_string data
        in
        let entry = Result.bind file ~f:(fun file -> Zipc.Member.make ~path:name (File file)) in
        Zipc.add (ok_exn entry) zip

      let add_file ?compress zip name path =
        add_entry ?compress zip name (In_channel.read_all path)

      let write zip path =
        Out_channel.write_all path ~data:(ok_exn (Zipc.to_binary_string zip))
    end

    let open_in = Zip.open_in

    module Builder = struct
      type t = {
        mutable manifest : manifest option;
        mutable files : (string option * Uri.t) list;
        mutable data : ([ `Name of string ] * string) list;
      }

      let create () = { manifest = None; files = []; data = [] }
      let embed_manifest b manifest = b.manifest <- Some manifest
      let put_file ?name b uri = b.files <- (name, uri) :: b.files
      let put_data b ~name ~data = b.data <- (`Name name, data) :: b.data

      let flush b uri =
        let path = Uri.(pct_decode (path uri)) in
        let zip =
          List.fold b.files ~init:Zipc.empty ~f:(fun zip (name, uri) ->
              let path = Uri.(pct_decode (path uri)) in
              let name = Option.value name ~default:path in
              Zip.add_file zip name path)
        in
        let zip =
          List.fold b.data ~init:zip ~f:(fun zip (`Name name, data) ->
              Zip.add_entry zip name data)
        in
        let man =
          match b.manifest with
          | Some man -> man
          | None -> Manifest.create "noname"
        in
        let mdata = Manifest.to_string man in
        Zip.write
          (Zip.add_entry ~compress:false zip Nameof.manifest mdata)
          path
    end

    let input b f = f (open_in b.path)

    let ( >>> ) = input

    let manifest b =
      b >>> fun zip ->
      let data = Zip.read_entry (Zip.find_entry zip Nameof.manifest) in
      Manifest.of_string data

    (* the paths of the URIs are percent-encoded, e.g., the backslashes
       of the Windows paths are %5C, so they are decoded *)
    let of_uri uri =
      let path = Uri.(pct_decode (path uri)) in
      let base = Filename.basename path in
      let name =
        if String.mem base '.' then Filename.chop_extension base else base
      in
      { name; path }

    let get_file ?name b uri =
      b >>> fun zip ->
      try
        let path = Uri.(pct_decode (path uri)) in
        let entry = Zip.find_entry zip path in
        let name = Option.value name ~default:path in
        Out_channel.write_all name ~data:(Zip.read_entry entry);
        Some (Uri.make ~path:name ())
      with Stdlib.Not_found -> None

    let get_data b name =
      b >>> fun zip ->
      try Some Zip.(read_entry (find_entry zip name))
      with Stdlib.Not_found -> None

    let list b =
      b >>> fun zip ->
      Zip.entries zip
      |> List.filter_map ~f:(fun e ->
          let name = Zip.filename e in
          Option.some_if (not (String.equal name Nameof.manifest)) name)

    let transform files bundle ~f =
      let zin = open_in bundle.path in
      let store filename data = Hashtbl.set files ~key:filename ~data in
      Zip.entries zin
      |> List.iter ~f:(fun entry ->
          let filename = Zip.filename entry in
          let process_file f =
            let name = Filename.temp_file "bundle" "entry" in
            Out_channel.write_all name ~data:(Zip.read_entry entry);
            f name;
            store filename (`Move name)
          in
          let process_data f =
            let data = Zip.read_entry entry in
            store filename (`Data (f data))
          in
          match f filename with
          | `Map f -> process_data f
          | `Proc f -> process_file f
          | `Copy -> process_file ignore
          | `Drop -> ());
      Hashtbl.fold files ~init:Zipc.empty ~f:(fun ~key:name ~data zout ->
          match data with
          | `Data s -> Zip.add_entry ~compress:false zout name s
          | `Copy f -> Zip.add_file ~compress:false zout name f
          | `Move f ->
              let zout = Zip.add_file ~compress:false zout name f in
              Sys.remove f;
              zout)
      |> Fn.flip Zip.write bundle.path

    let update bundle ~f = transform (String.Table.create ()) bundle ~f

    let insert bundle files =
      let files = String.Table.of_alist_exn files in
      transform files bundle ~f:(fun _ -> `Copy)

    let insert_files bundle files =
      insert bundle
        (List.map files ~f:(fun (name, uri) ->
             let path = Uri.(pct_decode (path uri)) in
             let name = Option.value name ~default:path in
             (name, `Copy path)))

    let insert_chunks bundle data =
      insert bundle
        (List.map data ~f:(fun (`Name name, data) -> (name, `Data data)))

    let insert_file ?name bundle file = insert_files bundle [ (name, file) ]

    let insert_data bundle ~name ~data =
      insert_chunks bundle [ (`Name name, data) ]

    let update_manifest bundle ~f =
      update bundle ~f:(fun file ->
          if String.equal file Nameof.manifest then
            `Map (fun s -> Manifest.(of_string s |> f |> to_string))
          else `Copy)
  end

  type bundle = Bundle.t

  let set_manifest_of_bundle bundle =
    try Manifest.update (Bundle.manifest bundle) with _ -> ()

  let set_main_bundle bundle =
    Bundle.main := bundle;
    set_manifest_of_bundle bundle

  let main_bundle () = Bundle.main.contents
end
