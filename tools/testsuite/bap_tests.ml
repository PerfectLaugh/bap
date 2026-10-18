(* the tests of bap that disassemble and lift the binaries *)

open Suite

let echos data =
  files data "bin" (fun name -> String.ends_with ~suffix:"-echo" name)

let echo target = "bin/" ^ target ^ "-echo"

(* [find_all name file args strs] checks that the output of bap on [file]
   with [args] contains every string of [strs] *)
let find_all name data file args strs =
  case name (fun env ->
      let out = bap env (path data file :: args) in
      List.iter (fun str -> contains env (name ^ " for " ^ str) out str) strs)

let api_main data =
  let main = "sub main(main_argc, main_argv, main_result)" in
  [
    ( "arm-linux-gnueabi",
      [
        "main_argc :: in u32 = R0";
        "main_argv :: in out u32 = R1";
        "main_result :: out u32 = R0";
      ] );
    ( "arm-linux-androideabi",
      [
        "main_argc :: in u32 = R0";
        "main_argv :: in out u32 = R1";
        "main_result :: out u32 = R0";
      ] );
    ( "i686-w64-mingw32",
      [
        "main_argc :: in u32 = mem[ESP + 4, el]:u32";
        "main_argv :: in out u32 = mem[ESP + 8, el]:u32";
        "main_result :: out u32 = EAX";
      ] );
    ( "x86_64-w64-mingw32",
      [
        "main_argc :: in u32 = low:32[RCX]";
        "main_argv :: in out u64 = RDX";
        "main_result :: out u32 = low:32[RAX]";
      ] );
    ( "x86_64-linux-gnu",
      [
        "main_argc :: in u32 = low:32[RDI]";
        "main_argv :: in out u64 = RSI";
        "main_result :: out u32 = low:32[RAX]";
      ] );
    ( "x86-linux-gnu",
      [
        "main_argc :: in u32 = mem[ESP + 4, el]:u32";
        "main_argv :: in out u32 = mem[ESP + 8, el]:u32";
        "main_result :: out u32 = EAX";
      ] );
    ( "mips-linux-gnu",
      [
        "main_argc :: in u32 = R4";
        "main_argv :: in out u32 = R5";
        "main_result :: out u32 = R2";
      ] );
    ( "mips64-linux-gnueabi",
      [
        "main_argc :: in u64 = R4";
        "main_argv :: in out u64 = R5";
        "main_result :: out u64 = R2";
      ] );
    ( "powerpc32-linux-gnu",
      [
        "main_argc :: in u32 = R3";
        "main_argv :: in out u32 = R4";
        "main_result :: out u32 = R3";
      ] );
  ]
  |> List.map (fun (target, lines) ->
      find_all ("api-main/" ^ target) data (echo target) [ "--dump=bir" ]
        (main :: lines))

(* [with_exit_code env name args expected status] checks that bap with
   [args] exits with [status] and outputs [expected] *)
let with_exit_code env name args expected status =
  let out = bap env args in
  check env
    ("got the expected exit status for the " ^ name)
    (out.status = Exited status);
  contains env ("got the right message for the " ^ name) out expected

(* the API files are searched in the API paths, or read in place, when
   they are specified with [--api-file] *)
let api_options data =
  [
    case "api-options" (fun env ->
        let api_path = file env "api" in
        Sys.mkdir api_path 0o755;
        Sys.mkdir (Filename.concat api_path "c") 0o755;
        ignore (write env "api/c/api-options.h" "");
        Sys.mkdir (file env "own") 0o755;
        let own = write env "own/api-options.h" "" in
        let api_file =
          write env "api-file.h" "int print_strings(char *a, int n);\n"
        in
        let echo = path data (echo "x86_64-linux-gnu") in
        List.iter
          (fun (name, args, expected, status) ->
            with_exit_code env name args expected status)
          [
            ( "api-show",
              [ "--api-path"; api_path; "--api-show" ],
              "api-options.h",
              0 );
            ( "list-paths",
              [ "--api-path"; api_path; "--api-list-paths" ],
              api_path,
              0 );
            ( "show api file",
              [ "--api-file"; "c:" ^ api_file; "--api-show" ],
              api_file,
              0 );
            ( "api file replaces api in path",
              [ "--api-path"; api_path; "--api-file"; "c:" ^ own; "--api-show" ],
              own,
              0 );
            ( "api file not existed",
              [ "--api-file"; "c:some_file" ],
              "can't find api",
              1 );
            ( "api file without language",
              [ "--api-file"; api_file ],
              "expected <lang>:<file>",
              1 );
            ( "api file applied",
              [ echo; "--dump=bir"; "--api-file"; "c:" ^ api_file ],
              "print_strings_a :: in out u64 = RDI",
              0 );
          ];
        let out =
          bap env
            [ "--api-path"; api_path; "--api-file"; "c:" ^ own; "--api-show" ]
        in
        check env "the replaced api in path isn't shown"
          (not
             (Re.execp
                (Re.compile (Re.str (Filename.concat api_path "c")))
                out.text)));
  ]

let byteweight data =
  echos data
  |> List.map (fun file ->
      let name = "byteweight/" ^ Filename.basename file in
      case name (fun env ->
          has env name
            (bap env [ path data file; "--dump=bir" ])
            "sub .*print_strings"))

let cache _ =
  [
    case "cache" (fun env ->
        (* a cache with exactly 10 MB of data *)
        let init n =
          let dir = file env (Printf.sprintf "cache-%d" n) in
          Sys.mkdir dir 0o755;
          ignore
            (bap env
               [
                 "cache";
                 "--size=5";
                 "--overhead=50";
                 "--cache-dir=" ^ dir;
                 "--disable-gc";
               ]);
          let data =
            List.fold_left Filename.concat dir [ ".cache"; "bap"; "data" ]
          in
          for x = 0 to 9 do
            Out_channel.with_open_bin
              (Filename.concat data (Printf.sprintf "entry.%d" x))
              (fun ch -> output_string ch (String.make 1048576 '\000'))
          done;
          dir
        in
        let check dir patterns =
          let out = bap env [ "cache"; "--info"; "--cache-dir=" ^ dir ] in
          List.iter (fun (re, name) -> has env name out re) patterns
        in
        let dir = init 0 in
        check dir
          [
            ("Capacity: * 5 MB", "set max_size");
            ("GC threshold: * 7 MB", "set threshold");
            ("Overhead: * 50 %", "set overhead");
            ("GC enabled: * false", "set no gc");
            ("Current size: * 10 MB", "gc disabled");
          ];
        ignore (bap env [ "cache"; "--cache-dir=" ^ dir; "--enable-gc" ]);
        check dir [ ("Current size: * 3 MB", "gc enabled") ];
        (* the collection runs on demand, even if it is disabled *)
        let dir = init 1 in
        ignore (bap env [ "cache"; "--run-gc"; "--cache-dir=" ^ dir ]);
        check dir [ ("Current size: * 3 MB", "run gc") ]);
  ]

let collator data =
  let base = path data "bin/arm-linux-gnueabi-echo" in
  [
    case "collator/base" (fun env ->
        has env "base is equal to base"
          (bap env [ "compare"; "callgraph"; base; base ])
          "the same callgraph");
    case ~slow:true "collator/all" (fun env ->
        let out =
          bap env
            ([ "compare"; "callgraph"; base ]
            @ List.map (path data) (echos data))
        in
        has env "base is in the set" out "is not different";
        has env "all other are different" out
          "Found 11 versions that are different");
  ]

(* reads the parameters from the configuration file of the user *)
let config data =
  let file = path data (echo "x86-linux-gnu") in
  [
    case "config" (fun env ->
        let dir = Filename.concat (Suite.file env "config") "bap" in
        Sys.mkdir dir 0o755;
        Out_channel.with_open_bin (Filename.concat dir "config") (fun ch ->
            output_string ch
              "# this is a testing configuration file\n\
               print-symbol = print_strings # this is an example of parameter\n");
        let out = bap env [ file; "--dump=bir" ] in
        lacks env "main is unexpected because not set in conf file" out
          "sub main";
        has env "reading parameters from conf file" out "sub print_strings";
        let out = bap env [ file; "--dump=bir"; "--print-symbol=main" ] in
        lacks env "print_strings is unexpected" out "sub print_strings";
        has env "overriding parameters in conf file" out "sub main");
  ]

let dasm_sec data =
  [
    find_all "disasm-section" data "bin/x86_64-linux-gnu-echo" [ "--dump=asm" ]
      [
        "Disassembly of section .init";
        "Disassembly of section .plt";
        "Disassembly of section .text";
      ];
  ]

let dyn data =
  [
    ("x86-coff-libvlc_dll", "libvlc_printerr", "libvlc_add_intf");
    ("x86_64-macho_dylib", "printf", "my_print");
    ("x86_64-elf_so", "foo", "bar");
  ]
  |> List.concat_map (fun (file, sym, caller) ->
      let file = path data ("dyn/" ^ file) in
      let matching sub =
        [ file; "--dump=bir"; "--print-matching=subroutine:" ^ sub ]
      in
      [
        case ("dynamic-libraries/" ^ sym) (fun env ->
            has env ("sub " ^ sym) (bap env (matching sym)) ("sub " ^ sym));
        case ("dynamic-libraries/call " ^ sym) (fun env ->
            has env ("call " ^ sym) (bap env (matching caller)) ("call @" ^ sym));
      ])

let echo_main data =
  echos data
  |> List.map (fun file ->
      let name = "echo-main/" ^ Filename.basename file in
      case name (fun env ->
          has env name (bap env [ path data file; "--dump=bir" ]) "sub .*main"))

let improper_feed _ =
  [
    ("empty file", "File corrupted", "");
    ("random data", "File format is not supported", "Hello, world\n");
    ( "truncated elf",
      "File format is not supported",
      "\x7f\x45\x4c\x46\x02\x01\x01\n" );
  ]
  |> List.map (fun (msg, expected, data) ->
      case ("improper-feed/" ^ msg) (fun env ->
          let file = write env "input" data in
          with_exit_code env msg [ file; "-d" ] expected 1))

let internal_plt data =
  [
    find_all "internal-plt" data "dyn/x86_64-elf_so"
      [
        "--dump=bir";
        "--read-symbols-from";
        path data "data/x86_64-elf_so.symbols";
      ]
      [ "call @foo with"; "call @bar@5b2 with" ];
  ]

(* the external symbols of a kernel module are synthetic subroutines *)
let kernel data =
  [
    find_all "kernel-modules" data "ko/arm-can-bcm.ko"
      [ "--dump=bir"; "--no-byteweight" ]
      [
        "sub kfree";
        "sub memcpy(memcpy_dst, memcpy_src, memcpy_n, memcpy_result)";
        "sub sprintf(sprintf_str, sprintf_format, sprintf_result)";
        "call @kfree";
        "call @memcpy";
        "call @sprintf";
      ];
  ]

let print_symbols =
  [ "--print-symbol-format=name"; "--print-symbol-format=addr" ]

let llvm_base data =
  (* the base is decimal *)
  let base = 40 in
  [
    ("arm-linux-gnueabi", 0x614);
    ("arm-linux-androideabi", 0x668);
    ("i686-w64-mingw32", 0x15c7);
    ("x86_64-w64-mingw32", 0x25a0);
    ("x86_64-linux-gnu", 0x76b);
    ("x86-linux-gnu", 0x5a4);
    ("x86_64-macho", 0xe50);
  ]
  |> List.map (fun (target, addr) ->
      let name = "llvm-base/" ^ target in
      case name (fun env ->
          let out =
            bap env
              ([ path data (echo target); "--dump=symbols"; "--loader=llvm" ]
              @ [ Printf.sprintf "--llvm-base=%d" base ]
              @ print_symbols)
          in
          has env name out (Printf.sprintf "main %x" (addr + base))))

(* the relocations of dysymtab are read in little and big endian files *)
let macho_loader data =
  [
    ("ko/powerpc-xnu-kext", "external-reference 45480 _abort");
    ("ko/x86_64-xnu-kext", "external-reference 18439 _memcmp");
  ]
  |> List.map (fun (file, expected) ->
      let name = "macho-loader/" ^ Filename.basename file in
      case name (fun env ->
          has env name
            (bap env [ path data file; "--dump=ogre"; "--no-objdump" ])
            expected))

let mangling data =
  [
    find_all "mangling" data "dyn/x86_64-elf_so"
      [
        "--dump=bir";
        "--read-symbols-from";
        path data "data/x86_64-elf_so.symbols";
      ]
      [ "sub bar"; "sub bar@5b2" ];
  ]

let obj data =
  let subs =
    [ "sum_external"; "sum_internal_1"; "sum_internal_2"; "sum_internal_3" ]
  in
  files data "obj" (fun _ -> true)
  |> List.map (fun file ->
      find_all
        ("object-files/" ^ Filename.basename file)
        data file [ "--dump=bir" ]
        (List.concat_map (fun sub -> [ "sub " ^ sub; "call @" ^ sub ]) subs))

(* all plugins are loaded *)
let plugins _ =
  [
    case "plugins" (fun env ->
        let plugins =
          (bap env [ "list"; "plugins" ]).text |> String.split_on_char '\n'
          |> List.filter_map (fun line ->
              match String.split_on_char ' ' line with
              | "" :: "" :: name :: _ when name <> "" -> Some name
              | _ -> None)
        in
        ignore (bap env [ "--version" ]);
        let log =
          {
            text =
              In_channel.with_open_bin (file env "log/log") In_channel.input_all;
            status = Exited 0;
          }
        in
        List.iter
          (fun plugin ->
            contains env (plugin ^ " was loaded") log ("Loaded " ^ plugin))
          plugins);
  ]

(* the recipes, the Primus Lisp files, and the Primus systems are used from
   their files, without installing them *)
let uninstalled data =
  let echo = path data (echo "x86_64-linux-gnu") in
  [
    case "uninstalled/recipe" (fun env ->
        let recipe = write env "dump.recipe" "(option dump bir)\n" in
        has env "the recipe at an absolute path is loaded"
          (bap env [ echo; "--recipe=" ^ recipe ])
          "sub main");
    case "uninstalled/lisp" (fun env ->
        let lisp =
          write env "uninstalled.lisp"
            "(defun uninstalled-lisp-function ()\n\
            \  \"is loaded from its file\"\n\
            \  0)\n"
        in
        has env "the lisp file is loaded"
          (bap env
             [
               echo;
               "--primus-lisp-load=posix," ^ lisp;
               "--primus-lisp-documentation";
             ])
          "uninstalled-lisp-function";
        has env "the missing lisp file is reported"
          (bap env [ echo; "--primus-lisp-load=missing.lisp" ])
          "unable to load the Primus Lisp file");
    case "uninstalled/systems" (fun env ->
        let asd =
          write env "uninstalled.asd"
            "(defsystem uninstalled:executor\n\
            \  :description \"is loaded from its file\"\n\
            \  :depends-on (bap:stubbed-executor))\n"
        in
        has env "the systems file is loaded"
          (bap env [ "primus-systems"; "--primus-systems-add-path=" ^ asd ])
          "uninstalled:executor");
  ]

let source_type _ =
  [
    case "source-type" (fun env ->
        let file = write env "code" "\x83\x3d\xe9\xb5\x21\x00\x01\xeb\xf7" in
        has env "source-type"
          (bap env [ file; "--dump=asm"; "--loader=raw"; "--raw-arch=x86" ])
          "cmpl");
  ]

let symbols data =
  [
    ("arm-linux-gnueabi", [ "main 8614"; "print_strings 85c4" ]);
    ("arm-linux-androideabi", [ "main 8668"; "print_strings 8618" ]);
    ("i686-w64-mingw32", [ "main 4015c7"; "print_strings 40159d" ]);
    ("x86_64-w64-mingw32", [ "main 4025a0"; "print_strings 40153b" ]);
    ("x86_64-linux-gnu", [ "main 40076b"; "print_strings 400733" ]);
    ("x86-linux-gnu", [ "main 80485a4"; "print_strings 804857a" ]);
    ("x86_64-macho", [ "main 100000e50"; "print_strings 100000df0" ]);
  ]
  |> List.map (fun (target, syms) ->
      find_all ("symbols/" ^ target) data (echo target)
        ("--dump=symbols" :: print_symbols)
        syms)

let version _ =
  [
    case "version" (fun env ->
        let out = bap env [ "--version" ] in
        lacks env "bap version has no errors" out "error";
        has env "bap version" out "1|2");
  ]

let tests =
  [
    api_main;
    api_options;
    byteweight;
    cache;
    collator;
    config;
    dasm_sec;
    dyn;
    echo_main;
    improper_feed;
    internal_plt;
    kernel;
    llvm_base;
    macho_loader;
    mangling;
    obj;
    plugins;
    source_type;
    symbols;
    uninstalled;
    version;
  ]
