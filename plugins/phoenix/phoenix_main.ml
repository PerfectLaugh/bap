open Core
open Bap.Std
open Format
include Self ()

let run options project =
  let arch = Project.arch project in
  let module Target = (val target_of_arch arch) in
  let module Phoenix = Phoenix_output.Make (struct
    let project = project
    let options = options

    module Target = Target
  end) in
  let dest = Phoenix.store () in
  printf "Stored data to %s@." dest

let labels_with : _ Config.param =
  let doc =
    "Put block name, assembler instructions, or bil instructions on\n\
    \     graph labels using `name', `asm', or `bil' respectively. Can be\n\
    \     specified as a list of multiple elements separated by commas."
  in
  let possibilities =
    [ ("name", `with_name); ("asm", `with_asm); ("bil", `with_bil) ]
  in
  Config.(
    param (list (enum possibilities)) ~default:[ `with_name ] "labels-with" ~doc)

let output_folder : string Config.param =
  let doc = "Output data into the specified folder" in
  Config.(param string ~default:"phoenix" "output-folder" ~doc)

let no_resolve : bool Config.param =
  let doc = "Do not resolve addresses to symbolic names" in
  Config.(flag "no-resolve" ~doc)

let keep_alive : bool Config.param =
  let doc = "Keep alive unused temporary variables" in
  Config.(flag "keep-alive" ~doc)

let no_inline : bool Config.param =
  let doc = "Disable inlining temporary variables" in
  Config.(flag "no-inline" ~doc)

let keep_consts : bool Config.param =
  let doc = "Disable constant folding" in
  Config.(flag "keep-const" ~doc)

let no_optimizations : bool Config.param =
  let doc = "Disable all kinds of optimizations" in
  Config.(flag "no-optimizations" ~doc)

let create output_folder cfg_format no_resolve keep_alive no_inline keep_consts
    no_optimizations =
  Phoenix_options.Fields.create ~output_folder ~cfg_format ~no_resolve
    ~keep_alive ~no_inline ~keep_consts ~no_optimizations

let man =
  [
    `S "DESCRIPTION";
    `P
      "Output information about processed binary in a human readable\n\
      \      format. This will emit CFG for each format in dot format. It\n\
      \      will also store BIL and ASM code in html format.Output folder\n\
      \      can be optionally specified. If omitted, the basename of the\n\
      \      target file will be used as a directory name.";
    `S "SEE ALSO";
    `P "$(b,bap-plugin-print)(1), $(b,text-tags)(3)";
  ]

let () =
  Config.manpage man;
  Config.declare_extension ~doc:"outputs the project in a phoenix format"
    ~provides:[ "printer" ] (fun { Config.get = ( ! ) } ->
      let options =
        create !output_folder !labels_with !no_resolve !keep_alive !no_inline
          !keep_consts !no_optimizations
      in
      Project.register_pass' (run options))
