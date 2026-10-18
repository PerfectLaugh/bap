open Core
open Bap_bundle.Std
open Bap_future.Std
open Or_error.Monad_infix
module Units = Bap_plugins_units.Make ()
module Package = Bap_plugins_package
module Filename = Stdlib.Filename
module Sys = Stdlib.Sys

module Plugin = struct
  type 'a or_error = 'a Or_error.t

  let args = ref Sys.argv
  let argv () = !args

  type body = Bundle of { path : string; bundle : bundle } | Package

  type t = {
    name : string;
    body : body;
    loaded : unit future;
    finish : unit promise;
  }

  let sexp_of_t { name } = sexp_of_string name

  type system_event =
    [ `Opening of string
    | `Loading of t
    | `Linking of string
    | `Loaded of t
    | `Errored of string * Error.t ]
  [@@deriving sexp_of]

  let system_events, event = Stream.create ()
  let notify (value : system_event) = Signal.send event value
  let load = Bap_plugins_loader_backend.load
  let setup_dynamic_loader = Bap_plugins_loader_backend.install

  (* loads the plugins that are packages, i.e., not bundles, by their
     names, the toplevel loads them with topfind, see bap_init_toplevel *)
  let package_loader = ref Bap_common.Plugins.load
  let setup_package_loader load = package_loader := load
  let init = lazy (Units.init ())

  let of_path path =
    try
      notify (`Opening path);
      let bundle = Bundle.of_uri (Uri.make ~path ()) in
      let name = Bundle.manifest bundle |> Manifest.name in
      let loaded, finish = Future.create () in
      { name; body = Bundle { path; bundle }; loaded; finish }
    with exn ->
      let err = Error.of_exn exn in
      notify (`Errored (path, err));
      raise exn

  let is_bundled = function { body = Bundle _ } -> true | _ -> false

  let of_package name =
    let loaded, finish = Future.create () in
    { name; body = Package; loaded; finish }

  let manifest p =
    match p.body with
    | Bundle { bundle } -> Bundle.manifest bundle
    | Package -> Manifest.create p.name

  let name p = p.name
  let desc p = manifest p |> Manifest.desc
  let tags p = manifest p |> Manifest.tags
  let cons p = manifest p |> Manifest.cons

  let load_unit ~reason ~name pkg : unit or_error =
    try
      notify (`Linking name);
      load pkg;
      Units.record name reason;
      Ok ()
    with
    | Dynlink.Error err -> Units.handle_error name reason err
    | exn -> Or_error.of_exn exn

  let is_debugging () =
    try String.(Sys.getenv "BAP_DEBUG" <> "0") with Stdlib.Not_found -> false

  let bundle = function
    | { body = Bundle { bundle } } -> bundle
    | _ -> assert false

  let path = function
    | { body = Bundle { path } } -> path
    | { name } -> sprintf "package:%s" name

  let loaded p = p.loaded
  let do_if_not_debugging f x = if is_debugging () then () else f x

  (* The unit is extracted from the bundle into a temporary file, which is
     removed after it is loaded. Windows doesn't remove the DLLs that are
     loaded, so there the unit is extracted into a file named after the
     digest of the bundle, which the next loads reuse, e.g., by another
     bap, which may have it loaded. *)

  (** [load_entry plugin name] loads a compilation unit with the specified
      [name] required by [plugin]. The compilation unit should not be already
      linked to the main program. The unit is looked in the plugin bundle first
      and, if not found, looked in the system using the [Findlib] library. If
      the [findlib] infrastructure is not available (and a unit wasn't found in
      the bundle) returns an error, otherwise returns unit.

      The loaded unit is recorded in the internal registry of units, linked into
      the host program (unless the `don't_register` option is set to [true]).

      We track compilation units by their names, where the name consists of the
      base name of library with the extension chopped. This is a slightly better
      granularity, than tracking only the library names, but still not the
      ideal. Ideally, this should be tracked by the language runtime.

      Note: we need to track loaded units in order to prevent the linking of the
      same compilation unit twice, as if that happens a memory of a unit is
      corrupted (the global roots are overwritten). This is a known bug/issue in
      the OCaml runtime that we need to workaround. *)
  let extracted_unit plugin name suffix =
    if not Sys.win32 then Filename.temp_file name suffix
    else
      let dir = Filename.concat (Filename.get_temp_dir_name ()) "bap-plugins" in
      (try Sys.mkdir dir 0o700 with Sys_error _ -> ());
      let digest = Stdlib.Digest.(to_hex (file (path plugin))) in
      Filename.concat dir (sprintf "%s-%s%s" name digest suffix)

  let load_entry ?(main = false) plugin name =
    let suffix = if Dynlink.is_native then ".cmxs" else ".cma" in
    let name = Filename.basename name in
    let dst = extracted_unit plugin name suffix in
    let entry = Uri.make ~path:(name ^ suffix) () in
    let reason =
      if main then `Provided_by plugin.name else `Requested_by plugin.name
    in
    let extracted =
      if Sys.win32 && Sys.file_exists dst then Some dst
      else
        Bundle.get_file ~name:dst (bundle plugin) entry
        |> Option.map ~f:(fun uri -> Uri.(pct_decode (path uri)))
    in
    match extracted with
    | Some path ->
        let result = load_unit ~reason ~name path in
        if not Sys.win32 then do_if_not_debugging Sys.remove path;
        result
    | None -> (
        match Package.resolve name with
        | Some lib ->
            let name = Filename.(basename name |> chop_extension) in
            load_unit ~reason ~name lib
        | None -> Or_error.error_string "dependency not found")

  let validate_unit _plugin main =
    match Units.lookup main with
    | None -> Ok ()
    | Some reason ->
        let with_whom =
          match reason with
          | `In_core -> "host program"
          | `Provided_by p -> "plugin " ^ p
          | `Requested_by p -> "library from plugin " ^ p
        in
        Or_error.errorf "a name %S clashes with a %s" main with_whom

  let validate_provided plugin mains =
    List.map mains ~f:(validate_unit plugin) |> Or_error.all_unit

  let load_entries plugin entries =
    List.fold entries ~init:(Ok ()) ~f:(fun so_far entry ->
        so_far >>= fun () ->
        match load_entry plugin entry with
        | Ok () -> Ok ()
        | Error err ->
            Or_error.errorf "Failed to load %s: %s" entry
            @@ Error.to_string_hum err)

  let is_missing dep = Option.is_none (Units.lookup dep)

  type context = unit -> unit

  let enter p =
    match p.body with
    | Bundle { bundle } ->
        let old = main_bundle () in
        set_main_bundle bundle;
        fun () -> set_main_bundle old
    | Package ->
        let old = Manifest.switch (Manifest.create p.name) in
        fun () -> Manifest.update old

  let leave f = f ()

  let with_context p ~f =
    let finally = enter p in
    protect ~f ~finally

  let try_load_bundled (plugin : t) =
    let (lazy ()) = init in
    notify (`Loading plugin);
    let m = manifest plugin in
    let mains = Manifest.provides m in
    validate_provided plugin mains >>= fun () ->
    let reqs = Manifest.requires m |> List.filter ~f:is_missing in
    let main = Manifest.main m in
    let old_bundle = main_bundle () in
    set_main_bundle (bundle plugin);
    load_entries plugin reqs >>= fun () ->
    load_entry ~main:true plugin main >>| fun () ->
    Promise.fulfill plugin.finish ();
    notify (`Loaded plugin);
    set_main_bundle old_bundle

  let try_load plugin =
    match plugin.body with
    | Bundle _ -> try_load_bundled plugin
    | Package -> (
        try
          notify (`Loading plugin);
          with_context plugin ~f:(fun () ->
              !package_loader plugin.name;
              Promise.fulfill plugin.finish ();
              notify (`Loaded plugin);
              Ok ())
        with exn -> Or_error.of_exn exn)

  let with_argv argv f =
    match argv with
    | None -> f ()
    | Some argv -> (
        let old = !args in
        args := argv;
        try
          let r = f () in
          args := old;
          r
        with exn ->
          args := old;
          raise exn)

  let do_load plugin =
    if Future.is_decided plugin.loaded then Ok ()
    else
      match try_load plugin with
      | Error err as result ->
          notify (`Errored (plugin.name, err));
          result
      | result -> result

  let load ?argv plugin = with_argv argv (fun () -> do_load plugin)
end

module Plugins = struct
  let paths_of_env () =
    let sep = if Sys.win32 then ';' else ':' in
    try Sys.getenv "BAP_PLUGIN_PATH" |> String.split ~on:sep
    with Stdlib.Not_found -> []

  let path = Bap_plugins_config.plugindir
  let is_bundle file = Filename.check_suffix file ".plugin"

  (* the library may contain plugin files, besides the directories *)
  let plugin_paths library =
    [ library; paths_of_env (); [ path ] ]
    |> List.concat
    |> List.filter ~f:Sys.file_exists
    |> List.filter ~f:(fun p -> Sys.is_directory p || is_bundle p)

  let has_feature requested features =
    match requested with
    | None -> true
    | Some requested -> List.exists features ~f:(Set.mem requested)

  let meets_constraint provided requirements =
    List.for_all requirements ~f:(Set.mem provided)

  let is_selected ~provides ~env p =
    has_feature provides (Plugin.tags p) && meets_constraint env (Plugin.cons p)

  let plugin_name = function Ok p -> Plugin.name p | Error (name, _) -> name

  let collect_bundles ?env ?provides ?(library = []) () =
    let ( / ) x y = x ^ "/" ^ y in
    let strset = Set.of_list (module String) in
    let provides = Option.map provides ~f:strset in
    let env = strset (Option.value env ~default:[]) in
    plugin_paths library
    |> List.concat_map ~f:(fun dir ->
        (if Sys.is_directory dir then
           Sys.readdir dir |> Array.to_list
           |> List.map ~f:(fun file -> dir / file)
         else [ dir ])
        |> List.filter_map ~f:(fun file ->
            if not (is_bundle file) then None
            else
              try
                let p = Plugin.of_path file in
                Option.some_if (is_selected ~provides ~env p) (Ok p)
              with exn -> Some (Error (file, Error.of_exn exn))))
    |> List.stable_sort ~compare:(fun x y ->
        String.compare (plugin_name x) (plugin_name y))
    (* a plugin in the library takes precedence over the plugins with the
       same name that are found after it *)
    |> List.remove_consecutive_duplicates ~which_to_keep:`First
         ~equal:(fun x y ->
           match (x, y) with
           | Ok x, Ok y -> String.equal (Plugin.name x) (Plugin.name y)
           | _ -> false)

  let list_bundles ?env ?provides ?library () =
    collect_bundles ?env ?provides ?library ()
    |> List.filter_map ~f:(function Ok p -> Some p | Error _ -> None)

  (* returns a sorted deduplicated list of dune plugin names.

     dune sites might have duplicating folders, so we have to be
     careful that we do not try to load the same plugin twice. *)
  let list_packages () =
    let require cnd k = if cnd then k () else None in

    (* for each occurence of [name] in the search paths
       returns its digest. The digest is the sum of md5 sums
       of all files that comprise the plugin folder. *)
    let digests name =
      Bap_common.Plugins.paths
      |> List.filter_map ~f:(fun dir ->
          let path = Filename.concat dir name in
          require (Sys.file_exists path) @@ fun () ->
          require (Sys.is_directory path) @@ fun () ->
          let contents =
            Sys.readdir path |> Array.map ~f:(Filename.concat path)
          in
          require (Array.length contents > 0) @@ fun () ->
          Option.return
          @@ Array.sum ~f:Md5.digest_file_blocking
               (module struct
                 type t = Md5.t

                 let zero = Md5.digest_string ""

                 let ( + ) x y =
                   Md5.digest_string (Md5.to_binary x ^ Md5.to_binary y)
               end)
               contents)
    in

    (* removes duplicating names provided that they have the same
       implementation. The implementation is digested as the md5 sum
       of files comprising the plugin folder.  *)
    let deduplicate names =
      let init = Map.empty (module String) in
      List.fold names ~init ~f:(fun plugins name ->
          Map.update plugins name ~f:(function
            | None -> digests name
            | Some ds -> ds @ digests name))
      |> Map.filteri ~f:(fun ~key:name ~data:digests ->
          match digests with
          | [] -> false
          | d :: ds when List.for_all ds ~f:(Md5.equal d) -> true
          | _ ->
              invalid_argf "The plugin %S has ambiguous implementations" name ())
      |> Map.keys
    in

    Bap_common.Plugins.list () |> deduplicate |> List.map ~f:Plugin.of_package

  let list ?env ?provides ?library () =
    list_packages () @ list_bundles ?env ?provides ?library ()

  let collect ?env ?provides ?library () =
    let packs = list_packages () |> List.map ~f:Result.return in
    let bunds = collect_bundles ?env ?provides ?library () in
    packs @ bunds

  let loaded, finished = Future.create ()

  let load ?argv ?env ?provides ?library ?(exclude = []) () =
    if Future.is_decided loaded then []
    else (
      Dynlink.allow_unsafe_modules true;
      let excluded = Set.of_list (module String) exclude in
      let r =
        collect ?env ?provides ?library ()
        |> List.filter_map ~f:(function
          | Error err -> Some (Error err)
          | Ok p when Set.mem excluded (Plugin.name p) -> None
          | Ok p -> (
              match Plugin.load ?argv p with
              | Ok () -> Some (Ok p)
              | Error err -> Some (Error (Plugin.path p, err))))
      in
      Promise.fulfill finished ();
      r)

  (* we will record all events from the plugin subsystem,
     and if a bad thing happens, we will dump the full history.
     We will clean the history once all plugins are loaded, to prevent
     a memory leak.  *)
  let setup_default_handler () =
    let events_backtrace = ref [] in
    Stream.observe Plugin.system_events (fun ev ->
        match ev with
        | `Errored (name, err) ->
            let backtrace =
              String.concat ~sep:"\n"
              @@ List.map !events_backtrace ~f:(fun ev ->
                  Format.asprintf "%a" Sexp.pp (Plugin.sexp_of_system_event ev))
            in
            Format.eprintf
              "An error has occurred while loading `%s': %a\n\n\
              \                          Events backtrace:\n\
               %s\n\n\
              \                          Aborting program ...\n\
               %!"
              name Error.pp err backtrace;
            exit 1
        | ev -> events_backtrace := ev :: !events_backtrace);
    Future.upon loaded (fun () -> events_backtrace := [])

  let run ?argv ?env ?provides ?(don't_setup_handlers = false) ?library ?exclude
      () =
    if not don't_setup_handlers then setup_default_handler ();
    let _ : (Plugin.t, string * Error.t) result list =
      load ?argv ?env ?provides ?library ?exclude ()
    in
    ()

  let events = Plugin.system_events

  type event = Plugin.system_event [@@deriving sexp_of]
end

module Std = struct
  type plugin = Plugin.t

  module Plugin = Plugin
  module Plugins = Plugins

  let setup_dynamic_loader = Plugin.setup_dynamic_loader
  let setup_package_loader = Plugin.setup_package_loader
  let list_loaded_units () = Units.list ()
end
