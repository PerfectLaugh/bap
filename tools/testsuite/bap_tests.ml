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
        let api_path = input "api-options/api" in
        let own = input "api-options/own/api-options.h" in
        let api_file = input "api-options/api-file.h" in
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
          let data = Filename.concat dir "data" in
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
        let dir = Suite.file env "config" in
        Out_channel.with_open_bin (Filename.concat dir "config") (fun ch ->
            output_string ch
              "# this is a testing configuration file\n\
               print-symbol = print_strings # this is an example of parameter\n");
        let out = bap env [ file; "--dump=bir"; "--config-dir=" ^ dir ] in
        lacks env "main is unexpected because not set in conf file" out
          "sub main";
        has env "reading parameters from conf file" out "sub print_strings";
        let out =
          bap env
            [ file; "--dump=bir"; "--config-dir=" ^ dir; "--print-symbol=main" ]
        in
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
    ("empty file", "File corrupted", "empty");
    ("random data", "File format is not supported", "random-data");
    (* the magic of ELF, and nothing else *)
    ("truncated elf", "File format is not supported", "truncated-elf");
  ]
  |> List.map (fun (msg, expected, name) ->
      case ("improper-feed/" ^ msg) (fun env ->
          let file = input ("improper-feed/" ^ name) in
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
          has env name (bap env [ path data file; "--dump=ogre" ]) expected))

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

(* the code after the jumps that never fall through, e.g., the junk
   after the traps, the calls to noreturn functions, and the jumps over
   the junk that overlaps their destinations, isn't disassembled *)
let branches data =
  let raw name arch ~junk ~real =
    case ("branches/" ^ name) (fun env ->
        let file = input ("branches/" ^ name ^ ".bin") in
        let out =
          bap env
            [
              file;
              "--loader=raw";
              "--raw-arch=" ^ arch;
              "--raw-entry-point=0";
              "--dump=asm";
            ]
        in
        has env (name ^ " keeps the destination") out real;
        lacks env (name ^ " drops the junk") out junk)
  in
  (* mov x0, #1; bl L; udf #0; udf #0; add x1, x1, #1; L: ret *)
  [
    raw "aarch64-udf" "aarch64" ~junk:"add x1" ~real:"ret";
    (* mov x0, #1; b.eq L; brk #1; add x1, x1, #1; add x1, x1, #1; L: ret *)
    raw "aarch64-brk" "aarch64" ~junk:"add x1" ~real:"ret";
    (* movl $1, %eax; call L; ud2; addq %rcx, %rax; L: retq *)
    raw "x86-ud2" "x86_64" ~junk:"addq" ~real:"retq";
    (* call L; the junk movl that overlaps L; L: addq %rcx, %rax; retq *)
    raw "x86-call-overlap" "x86_64" ~junk:"movl" ~real:"addq";
    (* jne L; the junk movl that overlaps L; L: addq %rcx, %rax; retq *)
    raw "x86-jne-overlap" "x86_64" ~junk:"movl" ~real:"addq";
    (* je L; jne L; the junk movl that overlaps L; L: addq; retq *)
    raw "x86-je-jne-overlap" "x86_64" ~junk:"movl" ~real:"addq";
    (* jmp L; the junk movl that overlaps L; L: addq %rcx, %rax; retq *)
    raw "x86-jmp-overlap" "x86_64" ~junk:"movl" ~real:"addq";
    case "branches/noreturn-calls" (fun env ->
        let out =
          bap env [ path data (echo "aarch64-linux-gnu"); "--dump=bir" ]
        in
        has env "abort doesn't return" out "call @abort with noreturn";
        has env "__stack_chk_fail doesn't return" out
          "call @__stack_chk_fail with noreturn");
  ]

(* the recipes, the Primus Lisp files, and the Primus systems are used from
   their files, without installing them *)
let uninstalled data =
  let echo = path data (echo "x86_64-linux-gnu") in
  [
    case "uninstalled/recipe" (fun env ->
        let recipe = input "uninstalled/dump.recipe" in
        has env "the recipe at an absolute path is loaded"
          (bap env [ echo; "--recipe=" ^ recipe ])
          "sub main");
    case "uninstalled/lisp" (fun env ->
        let lisp = input "uninstalled/uninstalled.lisp" in
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
        let asd = input "uninstalled/uninstalled.asd" in
        has env "the systems file is loaded"
          (bap env [ "primus-systems"; "--primus-systems-add-path=" ^ asd ])
          "uninstalled:executor");
  ]

(* the recompile pass writes the program as LLVM IR, with its runtime,
   which aren't compiled here, as the testsuite doesn't need clang *)
let recompile data =
  [
    case "recompile/x86_64-linux-gnu-crc-loop" (fun env ->
        let ll = file env "crc.ll" in
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-crc-loop";
              "--passes=recompile";
              "--recompile-output=" ^ ll;
            ]
        in
        check env "exits" (out.status = Exited 0);
        let ir = In_channel.with_open_bin ll In_channel.input_all in
        let has name text = contains env name { out with text = ir } text in
        has "defines main" "define internal void @f.main(i64 %ret)";
        has "calls putc natively" "call i64 @putc(";
        has "dispatches the indirect calls" "define void @bap_dispatch";
        has "starts from main" "call void @f.main(i64 %ret)";
        check env "writes the runtime" (Sys.file_exists (ll ^ ".rt.c")));
  ]

let source_type _ =
  [
    case "source-type" (fun env ->
        let file = input "source-type/code" in
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

(* the commands of analyze query the knowledge base of a project *)
let analyze data =
  let binary = path data (echo "x86_64-linux-gnu") in
  [
    case "analyze" (fun env ->
        let project = file env "echo.proj" in
        let out =
          bap env [ "disassemble"; binary; "--project=" ^ project; "--update" ]
        in
        check env "disassembled the project" (out.status = Exited 0);
        let analyze command =
          let out = bap env [ "analyze"; "--project=" ^ project; command ] in
          check env (command ^ " exited with 0") (out.status = Exited 0);
          lacks env (command ^ " has no errors") out "[Ee]rror";
          out
        in
        let out = analyze "units" in
        has env "units" out "file:.*x86_64-linux-gnu-echo bap:x86_64-gnu-elf";
        let unit =
          match String.split_on_char ' ' (String.trim out.text) with
          | unit :: _ -> unit
          | [] -> "file:" ^ binary
        in
        let out = analyze "subroutines" in
        List.iter
          (fun sub -> has env ("subroutines has " ^ sub) out (":0x" ^ sub))
          [ "40076b: main"; "400733: print_strings"; "400570: free" ];
        let out = analyze "subroutines :matches ma" in
        has env "matches main" out ":0x40076b: main";
        has env "matches malloc" out ":0x4005e0: malloc";
        lacks env "doesn't match free" out ": free";
        let out = analyze ("subroutine " ^ unit ^ " main") in
        sequence env out
          [
            ("the entry of main", ":0x40076b\n");
            ("the second instruction of main", ":0x40076c\n");
          ];
        lacks env "main doesn't have the instructions of free" out ":0x400570";
        let out = analyze ("subroutine " ^ unit ^ " main :semantics bap:bil") in
        sequence env out
          [
            ("the entry of main", ":0x40076b\n");
            (* the old value of the stack pointer is pushed, so the
               value is a temporary, see x86-move.lisp *)
            ( "push rbp",
              "#[0-9]+ := RBP.*RSP := RSP - 8.*mem := mem with \\[RSP, \
               el\\]:u64 <- #[0-9]+" );
            ("the second instruction of main", ":0x40076c\n");
            ("mov rbp, rsp", "RBP := RSP");
          ];
        let out = analyze "instructions" in
        has env "instructions of main" out ":main\n";
        has env "instructions of print_strings" out ":print_strings\n");
  ]

(* bap writes its cache and log only to the directories of the options, or
   of the variables, whose options prevail, and nothing to the home *)
let directories data =
  let binary = path data (echo "x86_64-linux-gnu") in
  let variables =
    [
      "BAP_CACHE_DIR";
      "BAP_LOG_DIR";
      "BAP_CONFIG_DIR";
      "XDG_CACHE_HOME";
      "XDG_CONFIG_HOME";
      "XDG_DATA_HOME";
      "XDG_STATE_HOME";
    ]
  in
  [
    case "directories" (fun env ->
        let dir name =
          let dir = file env name in
          Sys.mkdir dir 0o755;
          dir
        in
        let empty name dir = check env name (Sys.readdir dir = [||]) in
        let full name dir = check env name (Sys.readdir dir <> [||]) in
        let home = dir "home" in
        let homes =
          [
            ("HOME", home);
            ("USERPROFILE", home);
            ("APPDATA", home);
            ("LOCALAPPDATA", home);
          ]
        in
        let run ?(env' = []) args =
          let out =
            bap env ~env:(homes @ env') ~unset:variables (binary :: args)
          in
          check env
            ("bap " ^ String.concat " " args ^ " exited with 0")
            (out.status = Exited 0);
          has env "the output has main" out "sub main"
        in
        run [ "--dump=bir" ];
        empty "nothing is written to the home without directories" home;
        let cache = dir "cache-option" and log = dir "log-option" in
        let cache' = dir "cache-variable" and log' = dir "log-variable" in
        run
          ~env':[ ("BAP_CACHE_DIR", cache'); ("BAP_LOG_DIR", log') ]
          [ "--dump=bir"; "--cache-dir=" ^ cache; "--log-dir=" ^ log ];
        full "the cache is in the directory of the option" cache;
        full "the log is in the directory of the option" log;
        empty "the options prevail over the cache variable" cache';
        empty "the options prevail over the log variable" log';
        run
          ~env':[ ("BAP_CACHE_DIR", cache'); ("BAP_LOG_DIR", log') ]
          [ "--dump=bir" ];
        full "the cache is in the directory of the variable" cache';
        full "the log is in the directory of the variable" log';
        empty "nothing is written to the home with directories" home);
  ]

(* the identifiers of terms, which are numbered in their order, so that
   the summaries don't depend on the identifiers *)
let renumber text =
  let ids = Hashtbl.create 64 in
  let re =
    Re.(
      compile
        (seq [ alt [ bol; char '%' ]; group (repn xdigit 8 (Some 8)); eow ]))
  in
  Re.replace re text ~f:(fun group ->
      let tid = Re.Group.get group 1 in
      let id =
        match Hashtbl.find_opt ids tid with
        | Some id -> id
        | None ->
            let id = Hashtbl.length ids + 1 in
            Hashtbl.add ids tid id;
            id
      in
      let prefix = if (Re.Group.get group 0).[0] = '%' then "%" else "" in
      Printf.sprintf "%s#%d" prefix id)

(* the names of the anonymous subroutines, e.g., %00000560, which are
   their term identifiers, numbered in the order of their occurrences *)
let anonymous text =
  let names = Hashtbl.create 16 in
  let re = Re.(compile (seq [ char '%'; group (repn xdigit 8 (Some 8)) ])) in
  Re.replace re text ~f:(fun group ->
      let tid = Re.Group.get group 1 in
      let id =
        match Hashtbl.find_opt names tid with
        | Some id -> id
        | None ->
            let id = Hashtbl.length names + 1 in
            Hashtbl.add names tid id;
            id
      in
      Printf.sprintf "%%sub%d" id)

(* the summary of a program: its subroutines, with their arguments and the
   subroutines that they call, and the whole body of main *)
let summary text =
  let sub = Re.(compile (seq [ bol; repn xdigit 8 (Some 8); str ": sub " ])) in
  let call =
    Re.(compile (seq [ str "call @"; group (rep1 (diff any (set " \n"))) ]))
  in
  let subs =
    Re.split_delim sub text |> List.tl
    |> List.map (fun body ->
        let header = List.hd (String.split_on_char '\n' body) in
        let callees =
          Re.all call body
          |> List.map (fun group -> Re.Group.get group 1)
          |> List.sort_uniq String.compare
        in
        (header, body, callees))
  in
  let buf = Buffer.create 4096 in
  List.iter
    (fun (header, _, callees) ->
      Printf.bprintf buf "sub %s\n" header;
      if callees <> [] then
        Printf.bprintf buf "  calls %s\n" (String.concat " " callees))
    subs;
  let headers = anonymous (Buffer.contents buf) in
  Buffer.clear buf;
  Buffer.add_string buf headers;
  List.iter
    (fun (header, body, _) ->
      if String.starts_with ~prefix:"main(" header then
        Printf.bprintf buf "\nsub %s" (renumber body))
    subs;
  Buffer.contents buf

let status = function
  | Exited code -> Printf.sprintf "exited with %d" code
  | Signaled -> "was signaled"
  | Timeout -> "timed out"
  | Stopped -> "was stopped"

(* the golden summaries of the files of the testsuite, i.e., the
   specifications that the loaders make of them, and the programs that the
   lifters make, which detect the changes of the loaders, the lifters, the
   symbolizers, the stub resolvers, and the API. The files are the edge
   cases of the loaders and lifters: the layouts of src/loader, e.g., the
   images at the top of the address space, packed, PIE, TLS, weak, RWX and
   BSS segments, and the PE files, the stripped binaries, the object files,
   the shared libraries, the kernel modules, Mach-O, and the targets with
   their instruction sets, e.g., Thumb, and SSE *)
let golden data =
  List.concat_map
    (fun dir ->
      (* the programs of symexec differ only in main from the others *)
      files data dir (fun name ->
          not (Re.execp (Re.compile (Re.str "-symexec-")) name)))
    [ "bin"; "dyn"; "ko"; "obj"; "sse" ]
  |> List.map (fun name ->
      case ("golden/" ^ name) (fun env ->
          let file = path data name in
          (* the messages may have the name of the file *)
          let relative text =
            Re.replace_string (Re.compile (Re.str file)) ~by:name text
          in
          let out = bap env [ "specification"; file ] in
          golden env (name ^ ".spec")
            (Printf.sprintf "# %s\n%s" (status out.status) (relative out.text));
          let out = bap env [ file; "--dump=bir" ] in
          golden env (name ^ ".bir")
            (Printf.sprintf "# %s\n%s" (status out.status)
               (summary (relative out.text)))))

let tests =
  [
    analyze;
    api_main;
    api_options;
    branches;
    byteweight;
    cache;
    collator;
    config;
    dasm_sec;
    directories;
    dyn;
    echo_main;
    golden;
    improper_feed;
    internal_plt;
    kernel;
    llvm_base;
    macho_loader;
    mangling;
    obj;
    plugins;
    recompile;
    source_type;
    symbols;
    uninstalled;
    version;
  ]
