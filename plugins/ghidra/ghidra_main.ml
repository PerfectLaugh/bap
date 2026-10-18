open Core
open Bap_main

let ( / ) = Filename.concat

(* On Windows, dune installs the specifications in an archive, as it
   can't install directories there, which is extracted once into the
   cache, in the directory named after its digest, so that the archives
   of different builds don't mix. The archive is extracted into a
   temporary directory, which is renamed, so a concurrent bap that
   extracts it too, or an interrupted extraction, leave no partial
   specifications. Only the data of the processors that the decompiler
   loads is extracted, without their sources and the Sleigh sources of
   the specifications, as their paths may be too long for Windows. *)
let is_processor_data name =
  match String.split name ~on:'/' with
  | "Processors" :: _processor :: "data" :: _ :: _ ->
      not
        (List.exists [ ".slaspec"; ".sinc" ] ~f:(fun suffix ->
             String.is_suffix name ~suffix))
  | _ -> false

let extracted_archive site =
  let archive = site / "Ghidra" / "Processors.zip" in
  if not (Stdlib.Sys.file_exists archive) then site
  else
    (* a prefix of the digest, so that the paths stay short *)
    let digest = String.prefix Stdlib.Digest.(to_hex (file archive)) 12 in
    let root = Extension.Configuration.cachedir / ("ghidra-" ^ digest) in
    if not (Stdlib.Sys.file_exists root) then begin
      let rec mkdir dir =
        if not (Stdlib.Sys.file_exists dir) then begin
          mkdir (Filename.dirname dir);
          try Stdlib.Sys.mkdir dir 0o755 with Sys_error _ -> ()
        end
      in
      mkdir (Filename.dirname root);
      let tmp =
        Stdlib.Filename.temp_dir ~temp_dir:(Filename.dirname root) "ghidra-"
          ".tmp"
      in
      let zip = Zip.open_in archive in
      begin try
        Exn.protect
          ~finally:(fun () -> Zip.close_in zip)
          ~f:(fun () ->
            List.iter (Zip.entries zip) ~f:(fun entry ->
                let name = entry.Zip.filename in
                if (not entry.Zip.is_directory) && is_processor_data name then begin
                  let file = tmp / name in
                  mkdir (Filename.dirname file);
                  Zip.copy_entry_to_file zip entry file
                end))
      with exn ->
        FileUtil.rm ~recurse:true [ tmp ];
        raise exn
      end;
      try Stdlib.Sys.rename tmp root
      with Sys_error _ when Stdlib.Sys.file_exists root ->
        (* extracted by another bap *)
        FileUtil.rm ~recurse:true [ tmp ]
    end;
    root

(* the processor specifications built together with the plugin take
   precedence, mixing specifications of different Ghidra versions
   is not supported *)
let default_paths () =
  match
    List.filter (Bap_common.sites "ghidra") ~f:Stdlib.Sys.file_exists
    |> List.map ~f:extracted_archive
  with
  | [] ->
      Extension.Configuration.
        [ datadir / "ghidra"; sysdatadir / "ghidra"; "/usr/share/ghidra" ]
  | bundled -> bundled

let show_targets =
  Extension.Configuration.flag "list-targets" ~aliases:[ "targets" ]

let paths =
  Extension.Configuration.parameters Extension.Type.(list string) "path"

let () =
  Extension.declare
    ~doc:"provides loader, disassembler, and semantics using Ghidra Sleigh"
    ~provides:[ "disassembler"; "ghidra"; "lifter"; "semantics"; "p-code" ]
  @@ fun ctxt ->
  let open Extension.Syntax in
  Bap_ghidra.init ()
    ~paths:(List.concat (ctxt --> paths) @ default_paths ())
    ~print_targets:(ctxt --> show_targets);
  if ctxt --> show_targets then Error (Extension.Error.Exit_requested 0)
  else Ok ()
