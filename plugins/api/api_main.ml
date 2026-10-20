open Core
open Result.Monad_infix
open Bap_core_theory
open Bap.Std
module Sys = Stdlib.Sys
include Self ()
module Configuration = Bap_main.Extension.Configuration
module Sites = Api_sites

let try_with_default ~default f =
  match Result.try_with f with Ok r -> r | Error _ -> default

let getenv v = try Some (Sys.getenv v) with Stdlib.Not_found -> None

module Path = FilePath.DefaultPath.Abstract

type path = Path.filename
type api_descr = { lang : string; name : string }
type api = { desc : api_descr; path : path }

module Api_path = struct
  type t = path

  let ( / ) = Path.concat
  let to_string = Path.string_of_filename

  let of_string x = Path.reduce @@ Path.filename_of_string x
  let is_apiable = FileUtil.(Or (Is_file, Is_link))
  let try_with_access f p = try Ok (f p) with _ -> Error `No_access
  let exists p = try_with_access FileUtil.(test Exists) (to_string p)

  let is_apiable_path p =
    let r =
      exists p >>= fun x ->
      try_with_access (FileUtil.test is_apiable) (to_string p) >>= fun y ->
      Ok (x && y)
    in
    match r with Ok r -> r | _ -> false

  let is_dir p = try_with_access FileUtil.(test Is_dir) (to_string p)

  let find_files path =
    try_with_default ~default:[] (fun () ->
        FileUtil.find is_apiable (to_string path)
          (fun acc f -> of_string f :: acc)
          [])

  let with_lang path lang = path / of_string lang
  let lang_of_path path = to_string Path.(path |> reduce |> dirname |> basename)
  let name_of_path p = to_string @@ Path.basename p
  let desc_of_path p = { name = name_of_path p; lang = lang_of_path p }

  let api_of_path path =
    if is_apiable_path path then Some { desc = desc_of_path path; path }
    else None

  let find_apis ?lang path =
    let path' =
      match lang with Some lang -> with_lang path lang | None -> path
    in
    find_files path' |> List.filter_map ~f:api_of_path
end

module Api = struct
  type t = api

  let create lang path =
    let path = Api_path.of_string path in
    if Api_path.is_apiable_path path then
      let name = Api_path.name_of_path path in
      Some { desc = { lang; name }; path }
    else None
end

module Api_options = struct
  type t = {
    api_files : api list;
    list_paths : bool;
    show_apis : bool;
    api_paths : string list;
  }
  [@@deriving fields]
end

let env_paths =
  match getenv "BAP_API_PATH" with
  | None -> []
  | Some p -> Path.path_of_string p

let paths = List.map ~f:Api_path.of_string

let all_paths o =
  List.rev
  @@ List.concat
       [
         paths @@ Api_options.api_paths o;
         paths Sites.paths;
         env_paths;
         (paths
         @@ Configuration.
              [
                Filename.concat datadir "api"; Filename.concat sysdatadir "api";
              ]);
       ]
  |> List.filter ~f:(fun p ->
      match Api_path.is_dir p with Ok r -> r | Error _ -> false)

(* the files specified with [--api-file] are used in place, and replace
   the files with the same name in the API paths *)
let all_apis ?lang paths files =
  let files =
    match lang with
    | None -> files
    | Some lang ->
        List.filter files ~f:(fun api -> String.(api.desc.lang = lang))
  in
  let is_replaced api =
    List.exists files ~f:(fun file ->
        String.(
          file.desc.lang = api.desc.lang && file.desc.name = api.desc.name))
  in
  List.concat_map paths ~f:(Api_path.find_apis ?lang)
  |> List.filter ~f:(Fn.non is_replaced)
  |> fun apis -> apis @ files

let get_file file = Some file

let mapper paths files (module Api : Bap_api.S) =
  let files =
    all_apis ~lang:Api.language paths files
    |> List.map ~f:(fun api -> Api_path.to_string api.path)
  in
  Result.(Api.parse get_file files >>| Api.mapper)

(* the names of the functions that never return, from the api files of
   the languages that have a reader of them *)
let noreturn_functions paths files =
  all_apis paths files
  |> List.concat_map ~f:(fun api ->
      match Bap_api.noreturn_reader api.desc.lang with
      | None -> []
      | Some read -> (
          let file = Api_path.to_string api.path in
          match read file with
          | Ok names -> names
          | Error err ->
              info "can't find the noreturn functions in %s: %a" file Error.pp
                err;
              []))
  |> String.Set.of_list

(* a label is noreturn if it is a name, possibly versioned, e.g.,
   [exit@GLIBC_2.2.5], of a noreturn function *)
let promise_noreturn paths files =
  let open KB.Syntax in
  let names = lazy (noreturn_functions paths files) in
  KB.promise Theory.Label.is_noreturn @@ fun label ->
  KB.collect Theory.Label.name label >>| function
  | None -> None
  | Some name ->
      let name =
        Option.value_map ~default:name ~f:fst (String.lsplit2 name ~on:'@')
      in
      Option.some_if (Set.mem (Lazy.force names) name) true

(* The functions, that a file imports from the libraries, e.g., of
   KERNEL32, which the program calls through the slots of its import
   address table, or through the PLT entries, that have no names, e.g., of
   MIPS, that lld makes, have no subroutines, so they are the subroutines
   without addresses, as the external functions of the bare projects
   are, whose prototypes the api files give, so that the stubs, e.g., of
   Lisp, get their arguments. The data objects, that the programs import
   from msvcrt or libc, are not subroutines, so that the loaders give
   them storage, see primus_loader_basic.ml. *)
let data_objects =
  String.Set.of_list
    [
      "stdin";
      "stdout";
      "stderr";
      "environ";
      "__environ";
      "optarg";
      "optind";
      "opterr";
      "optopt";
      "__stack_chk_guard";
      "__progname";
      "program_invocation_name";
      "program_invocation_short_name";
      "__initenv";
      "__winitenv";
      "_acmdln";
      "_wcmdln";
      "_fmode";
      "_commode";
      "__argc";
      "__argv";
      "__wargv";
      "_environ";
      "_wenviron";
      "_iob";
      "__mb_cur_max";
      "_pctype";
      "_osver";
      "_winver";
      "_timezone";
      "_daylight";
      "_tzname";
    ]

let unversioned name =
  Option.value_map ~default:name ~f:fst (String.lsplit2 name ~on:'@')

let imports proj =
  match
    Ogre.eval
      (Ogre.collect Ogre.Query.(select (from Image.Scheme.external_reference)))
      (Project.specification proj)
  with
  | Ok refs ->
      let defined =
        Term.enum sub_t (Project.program proj)
        |> Seq.map ~f:Sub.name |> Seq.to_list |> String.Set.of_list
      in
      Seq.to_list refs
      |> List.map ~f:(fun (_, name) -> unversioned name)
      |> List.dedup_and_sort ~compare:String.compare
      |> List.filter ~f:(fun name ->
          not (Set.mem defined name || Set.mem data_objects name))
  | Error _ -> []

let with_imports imports prog =
  List.fold imports ~init:prog ~f:(fun prog name ->
      let tid = Tid.create () in
      Tid.set_name tid name;
      Term.append sub_t prog (Sub.create ~tid ~name ()))

(* the folders of the project, see [Bap_api.with_paths], are searched
   after those of the options *)
let main paths files proj =
  let imports = imports proj in
  let paths =
    paths
    @ List.filter_map (Bap_api.paths proj) ~f:(fun p ->
        let p = Api_path.of_string p in
        match Api_path.is_dir p with Ok true -> Some p | _ -> None)
  in
  Bap_api.processors () |> List.map ~f:(mapper paths files) |> Result.all
  |> function
  | Error e ->
      error "api wasn't applied: %a" Error.pp e;
      exit 1
  | Ok mappers ->
      Project.map_program proj ~f:(fun prog ->
          with_imports imports prog |> fun prog ->
          List.fold mappers ~init:prog ~f:(fun prog map -> map#run prog))

let list_of_paths paths =
  List.iter ~f:(fun p -> Format.printf "%s\n" (Api_path.to_string p)) paths

let show_all_apis paths files =
  let open Format in
  let pp_api api =
    printf "   %s : %s@." api.desc.name (Api_path.to_string api.path)
  in
  let print_lang apis =
    match apis with
    | [] -> ()
    | hd :: _ ->
        printf "@[<v>Language: %s@;" hd.desc.lang;
        List.iter ~f:pp_api apis;
        close_box ();
        print_newline ()
  in
  let apis =
    all_apis paths files
    |> List.stable_sort ~compare:(fun x y ->
        String.compare x.desc.lang y.desc.lang)
  in
  List.iter ~f:print_lang
    (List.group ~break:(fun x y -> String.(x.desc.lang <> y.desc.lang)) apis);
  printf "Total number of available API: %d\n" (List.length apis)

module Cmdline = struct
  let man =
    [
      `S "DESCRIPTION";
      `P "Automatically apply API bundled in the plugin. ";
      `S "SEE ALSO";
      `P "$(b,bap-api)(3), $(b,bap-plugin-frontc-parser)(1)";
    ]

  module Api = struct
    type t = api

    (* a path that starts with a drive of Windows, e.g., [C:\api.h], which
       has no language *)
    let is_drive_path str =
      Stdlib.Sys.win32
      && String.length str > 2
      && Char.is_alpha str.[0]
      && Char.equal str.[1] ':'
      && (Char.equal str.[2] '\\' || Char.equal str.[2] '/')

    let parser str =
      (* the file may be a Windows path, e.g., [c:C:\api.h] *)
      match String.lsplit2 str ~on:':' with
      | Some (lang, file) when not (is_drive_path str) -> (
          match Api.create lang file with
          | None -> `Error (sprintf "can't find api at %s" file)
          | Some api -> `Ok api)
      | Some _ | None -> `Error "expected <lang>:<file>"

    let printer ppf t =
      Format.fprintf ppf "%s:%s" t.desc.lang (Api_path.to_string t.path)

    let t =
      Config.converter parser printer
        { desc = { lang = ""; name = "" }; path = Api_path.of_string "" }
  end

  let api_files : Api.t list list Config.param =
    let doc =
      "Use the specified api module(s), which are read from their\n\
      \      files, without installing them. Each module should be of the\n\
      \      form <lang>:<file>, where <lang> is the language in which API\n\
      \      is written, and <file> is a path to the specification. A module\n\
      \      replaces the module with the same name in the api paths.\n\
      \      Multiple modules can be used by specifying this option several\n\
      \      times."
    in
    Config.(param_all (list Api.t) "file" ~doc)

  let list_paths =
    let doc = "List of all registered paths" in
    Config.(flag "list-paths" ~doc)

  let show_apis =
    let doc = "Show all registered api" in
    Config.(flag "show" ~doc)

  let path =
    let doc =
      "Add a list of a paths where to search apis, each api is stored\n\
      \      in the folder named after its language, e.g., $(b,PATH/c/api.h)"
    in
    Config.(param (list dir) "path" ~doc ~default:[])

  let dispatch_flags o =
    let open Api_options in
    match (o.list_paths, o.show_apis) with
    | false, false -> ()
    | show_paths, show_apis ->
        let paths = all_paths o in
        if show_paths then list_of_paths paths;
        if show_apis then show_all_apis paths o.api_files;
        exit 0

  let dispatch o =
    let paths = all_paths o in
    dispatch_flags o;
    promise_noreturn paths (Api_options.api_files o);
    Project.register_pass ~autorun:true ~deps:[ "abi" ]
      (main paths (Api_options.api_files o))

  let normalize_paths ps =
    let norm p = if String.equal p "." then Sys.getcwd () else p in
    List.map ~f:norm ps

  let () =
    Config.manpage man;
    Config.declare_extension ~doc:"inserts subroutines arg terms"
      ~provides:[ "abi"; "api"; "pass" ]
    @@ fun { Config.get = ( ! ) } ->
    let api_paths = normalize_paths !path in
    dispatch
      (Api_options.Fields.create ~api_files:(List.concat !api_files)
         ~list_paths:!list_paths ~show_apis:!show_apis ~api_paths)
end
