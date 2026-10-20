(** Builds BAP Annotated Reference.

    The API reference is taken from the odoc output of [dune build @doc], which
    must be built before running this tool. *)

open Core
open Poly
open Bap_plugins.Std
module Sys = Stdlib.Sys
module Filename = Stdlib.Filename

let libraries =
  [
    ( "Core libraries",
      [
        ("bap-main", "Bap_main", "", "the entry point to BAP");
        ( "bap-knowledge",
          "Bap_knowledge.Knowledge",
          "Bap_knowledge",
          "The Knowledge Representation library" );
        ("bap-core-theory", "Bap_core_theory", "", "The Core Theory Library");
        ("bap-std", "Bap.Std", "", "The Standard Library");
        ( "bap-taint",
          "Bap_taint.Std",
          "Bap_taint",
          "The Taint Analysis Framework" );
        ( "bap-primus",
          "Bap_primus.Std",
          "Bap_primus",
          "The Microexecution Framework" );
      ] );
    ( "Foundation Libraries",
      [
        ("monads", "Monads.Std", "Monads", "The Monads library");
        ("regular", "Regular.Std", "Regular", "Regular Data Library");
        ("graphlib", "Graphlib.Std", "Graphlib", "Algorithms on graphs");
        ("bitvec", "Bitvec", "", "Bitvectors and modular arithmetic");
        ( "bitvec-binprot",
          "Bitvec_binprot",
          "",
          "Provides Binprot serialization for bitvectors" );
        ( "bitvec-sexp",
          "Bitvec_sexp",
          "",
          "Provides s-exp serialization for bitvectors" );
        ( "bitvec-order",
          "Bitvec_order",
          "",
          "Implements Janestreet comparators for bitvectors" );
        ("bap-future", "Bap_future.Std", "Bap_future", "Futures and Streams");
        ("ogre", "Ogre", "", "A sexp-based NoSQL database");
      ] );
    ( "Hardware Specific Libraries",
      [
        ("bap-arm", "ARM", "", "ARM definitions");
        ("bap-x86", "X86_cpu", "", "x86/x86-64 definitions");
        ("bap-mips", "Bap_mips_target", "", "MIPS definitions");
        ("bap-powerpc", "Bap_powerpc_target", "", "PowerPC definitions");
        ("bap-riscv", "Bap_riscv_target", "", "RISCV definitions");
        ("bap-systemz", "Bap_systemz_target", "", "SystemZ definitions");
      ] );
    ( "Language and API/ABI Specific Libraries",
      [
        ("bap-abi", "Bap_abi", "", "Interface for specifying ABI");
        ("bap-api", "Bap_api", "", "Interface for defining API");
        ("bap-c", "Bap_c.Std", "Bap_c", "Basic definitions of the C language");
      ] );
    ( "Analyses and Auxiliary Libraries",
      [
        ( "bap-primus-track-visited",
          "Bap_primus_track_visited",
          "",
          "The interface to the Primus coverage monitoring component" );
        ( "bap-beagle",
          "Beagle_prey",
          "",
          "An interface to the Beagle string deobfuscation analysis" );
      ] );
    ( "Utility Libraries",
      [
        ("bap-bml", "Bap_bml", "", "writing term transformations");
        ( "bare",
          "Bare",
          "",
          "writing rules for matching for Primus observations" );
        ( "bap-bundle",
          "Bap_bundle.Std",
          "Bap_bundle",
          "creating and opening bundles" );
        ("bap-build", "Bap_build.Std", "Bap_build", "building bapbuild plugins");
        ( "bap-byteweight",
          "Bap_byteweight",
          "",
          "interface to the Byteweight subsystem" );
        ( "bap-demangle",
          "Bap_demangle.Std",
          "Bap_demangle",
          "writing name demanglers" );
        ("bap-dwarf", "Bap_dwarf.Std", "Bap_dwarf", "a native DWARF parser");
        ("bap-elf", "Bap_elf.Std", "Bap_elf", "a native ELF parser");
        ( "bap-llvm",
          "Bap_llvm.Std",
          "Bap_llvm",
          "an inteface to LLVM disassemblers and loaders" );
        ("bap-ghidra", "Bap_ghidra", "Bap_ghidra", "an inteface to Ghidra");
        ("bap-plugins", "Bap_plugins.Std", "Bap_plugins", "loading plugins");
        ( "bap-recipe",
          "Bap_recipe",
          "",
          "loading recipes (packs of command line arguments)" );
        ( "bap-strings",
          "Bap_strings.Std",
          "Bap_strings",
          "various text utilities" );
        ( "bap-relation",
          "Bap_relation",
          "",
          "A representation of relations between two sets" );
        ( "bap-traces",
          "Bap_traces.Std",
          "Bap_traces",
          "working with execution traces" );
        ("text-tags", "Text_tags", "", "Extension of Format's semantic tags");
      ] );
  ]

let frontends =
  [
    ("bap", "bap main frontend");
    ("bap-byteweight", "create, obtain and evaluate byteweight signatures");
  ]

let introduction =
  {|
<h2>Introduction</h2>

<p>
The Carnegie Mellon University Binary Analysis Platform (CMU BAP) is a
suite of utilities and libraries that enables analysis of programs in
their machine representation. BAP is written in OCaml, relies on
dynamically loaded plugins for extensibility, and is widely used for
security analysis, program verification, and reverse engineering.</p>

<p>The framework consists of a bunch of libraries, plugins and
frontends. The libraries provide code reusability, plugins facilitate
extensibility and frontends serve as entry points.</p>

<p>Frontends come with comprehensive manuals,
that can be accessed by using <code>--help</code> command line options, or via
the <code>man</code> command, if the manpath is configured correctly.
Finally, you can access a man page for a plugin using
<code>--&lt;PLUGIN&gt;-help</code> command line option of a frontend, e.g.,
<code>bap --map-terms-help</code>.</p>
|}

let packages =
  List.concat_map
    ~f:(fun (_, ps) -> List.map ~f:(fun (p, _, _, _) -> p) ps)
    libraries

let mkdir path = if not (Sys.file_exists path) then Caml_unix.mkdir path 0o770

(* runs the program, without a shell, with the files as its standard input
   and output, and returns its exit code *)
let exec ?input ?output ?(append = false) prog args =
  let open Caml_unix in
  let fin = Option.map input ~f:(fun f -> openfile f [ O_RDONLY ] 0) in
  let flags = if append then [ O_APPEND ] else [ O_TRUNC ] in
  let fout =
    Option.map output ~f:(fun f ->
        openfile f ([ O_WRONLY; O_CREAT ] @ flags) 0o644)
  in
  let close () =
    Option.iter fin ~f:close;
    Option.iter fout ~f:close
  in
  match
    create_process prog
      (Array.of_list (prog :: args))
      (Option.value fin ~default:Caml_unix.stdin)
      (Option.value fout ~default:Caml_unix.stdout)
      Caml_unix.stderr
  with
  | exception exn ->
      close ();
      raise exn
  | pid -> (
      close ();
      match snd (waitpid [] pid) with WEXITED n -> n | _ -> 1)

let run ?input ?output ?append prog args =
  if exec ?input ?output ?append prog args <> 0 then
    failwithf "Command: '%s' failed" (String.concat ~sep:" " (prog :: args)) ()

let append_to_file file data =
  Out_channel.with_file ~append:true file ~f:(fun ch ->
      Out_channel.output_string ch data)

(* the odoc output of [dune build @doc], relative to the doc folder *)
let odoc_html = "../_build/default/_doc/_html"

let escape_html s =
  String.concat_map s ~f:(function
    | '<' -> "&lt;"
    | '>' -> "&gt;"
    | '&' -> "&amp;"
    | '"' -> "&quot;"
    | c -> String.of_char c)

let render_entry (pkg, entry, short, desc) =
  let name_to_display = match short with "" -> entry | _ -> short in
  let path = String.substr_replace_all entry ~pattern:"." ~with_:"/" in
  sprintf {|<li><a href="%s/%s/index.html"><code>%s</code></a> - %s</li>|} pkg
    path name_to_display (escape_html desc)

let render_section (name, entries) =
  sprintf "<h3>%s</h3>\n<ul>\n%s\n</ul>" name
    (String.concat ~sep:"\n" @@ List.map ~f:render_entry entries)

(* the name of the manual page of a tool and the command of its help *)
type info = { man : string -> string; help : string -> string * string list }

let program = { man = Fn.id; help = (fun tool -> (tool, [ "--help=groff" ])) }

let plugin =
  {
    man = sprintf "bap-plugin-%s";
    help = (fun name -> ("bap", [ sprintf "--%s-help=groff" name ]));
  }

let generate_man3_redirection lib =
  mkdir "man3";
  let redirection =
    sprintf
      {|
    <!doctype html>
    <html>
    <head>
    <meta http-equiv="refresh" content="0; url='../odoc/%s/index.html'" />
    </head>
    <body></body>
    </html> |}
      lib
  in
  let name = sprintf "man3/%s.3.html" lib in
  Out_channel.write_all name ~data:redirection

(* renders the help of the tool, in groff, with man2html *)
let build_manual { man; help } tool =
  mkdir "man1";
  let prog, args = help tool in
  let groff = Filename.temp_file "bapdoc" ".groff"
  and html = Filename.temp_file "bapdoc" ".html" in
  protect
    ~finally:(fun () ->
      Sys.remove groff;
      Sys.remove html)
    ~f:(fun () ->
      match exec ~output:groff prog args with
      | 0 ->
          (* the minus signs, which groff writes as \N'45', are hyphens *)
          In_channel.read_all groff
          |> String.substr_replace_all ~pattern:{|\N'45'|} ~with_:"-"
          |> fun data ->
          Out_channel.write_all groff ~data;
          run ~input:groff ~output:html "man2html" [ "-r" ];
          In_channel.read_all html
          |> String.substr_replace_all ~pattern:"../index.html"
               ~with_:"../odoc/index.html"
          |> fun data ->
          Out_channel.write_all (sprintf "man1/%s.1.html" (man tool)) ~data
      | _ ->
          eprintf "Warning: can't render manpage for %s\n" tool;
          eprintf "Called as %S, got:\n%s\n%!"
            (String.concat ~sep:" " (prog :: args))
            (In_channel.read_all groff))

let generate_manual () =
  let _frontends =
    List.iter frontends ~f:(fun (p, _) -> build_manual program p)
  in
  let _plugins =
    Plugins.list ()
    |> List.iter ~f:(fun p -> build_manual plugin (Plugin.name p))
  in
  List.iter packages ~f:generate_man3_redirection

let plugins =
  let by_plugin_name p1 p2 = String.compare (Plugin.name p1) (Plugin.name p2) in
  Plugins.list ()
  |> List.sort ~compare:by_plugin_name
  |> List.fold ~init:"" ~f:(fun s p ->
      Format.sprintf "%s%-24s %s\n" s (Plugin.name p) (Plugin.desc p))

let plugins_index =
  sprintf "\n<h2>Plugins</h2>\n<pre>%s</pre>\n" (escape_html plugins)

let library_index =
  sprintf "\n<h2>Libraries</h2>\n%s"
    (List.map ~f:render_section libraries |> String.concat ~sep:"\n\n")

let index_page =
  sprintf
    {|<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>BAP API</title>
<link rel="stylesheet" href="odoc.support/odoc.css">
</head>
<body class="odoc">
<header class="odoc-preamble"><h1>BAP API</h1></header>
<div class="odoc-content">
%s
%s
%s
</div>
</body>
</html>
|}
    introduction library_index plugins_index

(* copies the API reference built by odoc and adds the index page *)
let generate () =
  if Sys.file_exists "odoc" then FileUtil.rm ~recurse:true [ "odoc" ];
  FileUtil.cp ~recurse:true [ odoc_html ] "odoc";
  Out_channel.write_all "odoc/index.html" ~data:index_page

let install_handwritten_manpages () =
  mkdir "man1";
  Sys.readdir "../man"
  |> Array.iter ~f:(fun page ->
      FileUtil.cp
        [ Filename.concat "../man" page ]
        (Filename.concat "man1" page))

(* by default, title is the buffer/file name with no extension,
   that's why we need override it with an empty title *)
let html_of_org file =
  append_to_file file "#+TITLE: Primus Lisp Documentation\n\n";
  run "emacs" [ file; "--batch"; "--eval"; "(org-html-export-to-html)" ];
  Sys.remove file

let install_lisp_documentation ?(option = "") target =
  let file = Filename.concat target "index.org" in
  mkdir target;
  let options = if String.is_empty option then [] else [ option ] in
  run ~output:file "bap" ("primus-lisp-documentation" :: options);
  html_of_org file

let install_primus_api () =
  let file = "primus/index.org" in
  let add x =
    append_to_file file (sprintf "* %s\n" (String.capitalize x));
    run ~output:file ~append:true "bap" [ "primus-" ^ x ]
  in
  mkdir "primus";
  List.iter ~f:add [ "systems"; "components"; "observations" ];
  html_of_org file

(* the program is in PATH, with an executable suffix on Windows *)
let is_installed x =
  let sep = if Sys.win32 then ';' else ':' in
  let suffixes = if Sys.win32 then [ ""; ".exe"; ".cmd"; ".bat" ] else [ "" ] in
  Option.value (Sys.getenv_opt "PATH") ~default:""
  |> String.split ~on:sep
  |> List.exists ~f:(fun dir ->
      List.exists suffixes ~f:(fun suffix ->
          Sys.file_exists (Filename.concat dir (x ^ suffix))))

let check_installed x =
  if not (is_installed x) then failwith (sprintf "%s is not installed\n" x)

let check () =
  check_installed "bap";
  check_installed "emacs";
  check_installed "man2html";
  if not (Sys.file_exists odoc_html) then
    failwithf "%s is not found, run `dune build @doc` first\n" odoc_html ()

let () =
  (* the website is generated in doc/, when the tool is run from the root
     of the repository, as dune exec -- ./tools/bapdoc.exe *)
  if Sys.file_exists "dune-project" then begin
    mkdir "doc";
    Sys.chdir "doc"
  end;
  check ();
  generate_manual ();
  install_handwritten_manpages ();
  install_lisp_documentation "lisp";
  install_lisp_documentation ~option:"--semantics" "semantics";
  install_primus_api ();
  generate ()
