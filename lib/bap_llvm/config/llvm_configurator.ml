open Base
open Stdio
module C = Configurator.V1
module Buf = Stdlib.Buffer
module Arg = Stdlib.Arg
module Filename = Stdlib.Filename

(* the stubs initialize only the infos, the machine code layers, and the
   disassemblers of the targets, see llvm_disasm.cpp, so they link only
   these components of each target, not all-targets, whose code
   generators are the most of LLVM *)
let target_components targets =
  List.concat_map targets ~f:(fun target ->
      let target = String.lowercase target in
      [ target ^ "info"; target ^ "desc"; target ^ "disassembler" ])

let llvm_components =
  [
    "binaryformat";
    "core";
    "mc";
    "debuginfodwarf";
    "debuginfomsf";
    "debuginfopdb";
  ]

(* the llvm-config of the LLVM that libllvm builds from its sources *)
let llvm_config = ref ""

(* llvm-config reports the absolute paths of the LLVM in the sandbox of
   the rule, which are replaced with the paths of the LLVM in the build
   tree, relative to the directories where they are used: the C++ stubs
   are compiled in the directory of the library, and the programs are
   linked in the root of the build context *)
let compile_prefix = ref ""
let link_prefix = ref ""
let slashify = String.tr ~target:'\\' ~replacement:'/'

let llvm ?prefix self opts =
  let flags =
    C.Process.run_capture_exn self !llvm_config opts
    |> String.strip |> C.Flags.extract_blank_separated_words
  in
  match prefix with
  | None -> flags
  | Some prefix ->
      let llvm =
        slashify @@ String.strip
        @@ C.Process.run_capture_exn self !llvm_config [ "--prefix" ]
      in
      List.map flags ~f:(fun flag ->
          String.substr_replace_all (slashify flag) ~pattern:llvm ~with_:prefix)

let filename = ref ""

let args =
  [
    ("-filename", Arg.Set_string filename, "NAME the name of the file");
    ("-llvm-config", Arg.Set_string llvm_config, "PATH the llvm-config to use");
    ( "-compile-prefix",
      Arg.Set_string compile_prefix,
      "PATH the LLVM relative to the directory of the library" );
    ( "-link-prefix",
      Arg.Set_string link_prefix,
      "PATH the LLVM relative to the root of the build context" );
  ]

let () =
  C.main ~args ~name:"bap-llvm" @@ fun self ->
  if Filename.is_relative !llvm_config then
    llvm_config := Filename.concat (Stdlib.Sys.getcwd ()) !llvm_config;
  let linkmode =
    "--link-" ^ String.strip
    @@ C.Process.run_capture_exn self !llvm_config [ "--shared-mode" ]
  in
  C.Flags.write_sexp "link.flags"
  @@ List.concat
       [
         llvm self ~prefix:!link_prefix [ linkmode; "--ldflags" ];
         llvm self
           ([ linkmode; "--libs" ]
           @ target_components (llvm self [ "--targets-built" ])
           @ llvm_components);
         (* the system libraries depend on the link mode and on how
            LLVM was configured, e.g., a shared LLVM needs none *)
         llvm self [ linkmode; "--system-libs" ];
         (* the runtime of C++ is in ../bap_disasm/cxx_runtime.flags *)
       ];
  (* the C stubs and llvm_register.cpp call the functions of the program,
     the runtime of OCaml and the disassembler of BAP, which flexdll can't
     relocate on Windows when the plugin is further than 2 GB from the
     program, as the calls are relative, so they are absolute in the large
     model, in which the references to all symbols are indirect, of which
     flexlink makes a section each, so the rest isn't in this model *)
  let code_model = if Stdlib.Sys.win32 then [ "-mcmodel=large" ] else [] in
  C.Flags.write_sexp "c.flags" code_model;
  C.Flags.write_sexp "cxx.flags"
  @@ List.concat
       [
         (* all code is position-independent on Windows *)
         (if Stdlib.Sys.win32 then [] else [ "-fPIC" ]);
         llvm self ~prefix:!compile_prefix [ "--cxxflags" ];
       ];
  let version =
    String.strip @@ C.Process.run_capture_exn self !llvm_config [ "--version" ]
  in
  let src = !filename in
  let dst = Stdlib.Filename.chop_extension src in
  In_channel.with_file src ~f:(fun input ->
      Out_channel.with_file dst ~f:(fun output ->
          In_channel.iter_lines input ~f:(fun line ->
              let buf = Buffer.create (String.length line + 1) in
              Buf.add_substitute buf
                (function "llvm_version" -> version | s -> s)
                line;
              Buf.add_char buf '\n';
              Buf.output_buffer output buf)))
