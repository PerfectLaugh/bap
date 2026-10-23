(* the tests of bap that run the binaries in the emulator *)

open Suite

(* runs the floating-point test of src/floats.c, which performs addition,
   division and comparison and prints PASS seven times, in the interpreter,
   which runs the lifted code *)
let floats name args data =
  [
    case name (fun env ->
        let out =
          bap env
            ((path data "sse/floats" :: args)
            @ [ "--passes=run"; "--run-systems=bap:legacy-main" ])
        in
        let passes = count out "PASS" in
        check env
          (Printf.sprintf "expected 7 passes, got %d" passes)
          (passes = 7));
  ]

(* the flattened control flows, by hand, of src/cff.c, and by
   Obfuscator-LLVM, of src/ollvm/collatz.c, whose blocks go through the
   dispatchers, run as the original *)
let cff data =
  List.concat_map
    (fun bin ->
      List.map
        (fun system ->
          case
            ("run/" ^ bin ^ "/" ^ system)
            (fun env ->
              let out =
                bap env
                  [
                    path data ("bin/x86_64-linux-gnu-" ^ bin);
                    "--passes=run";
                    "--run-systems=" ^ system;
                  ]
              in
              contains env "prints the steps" out "53\n111\n"))
        [ "bap:stubbed-executor"; "bap:unicorn-executor" ])
    [ "cff"; "ollvm-fla" ]

let sse = floats "llvm-x86-64-sse" []
let x86_floats = floats "x86-floats" [ "--bil-enable-fp-emulation" ]

(* the api of PowerPC is not the default one *)
let api data file =
  if String.starts_with ~prefix:"powerpc" (Filename.basename file) then
    [ "--api-path=" ^ path data "api/powerpc" ]
  else []

let run data =
  let expected =
    [
      "hello";
      "cruel";
      "world";
      "we";
      "not";
      "are";
      "some";
      "thine";
      "the";
      "be";
      "course";
    ]
  in
  List.concat_map
    (fun bin ->
      List.map
        (fun system ->
          let file = "bin/" ^ bin in
          let name = Printf.sprintf "run/%s/%s" system bin in
          case name (fun env ->
              let out =
                bap env
                  ([ path data file; "--run-argv=hello,cruel,world" ]
                  @ [ "--primus-lisp-type-check"; "--passes=run" ]
                  @ api data file
                  @ [ "--run-systems=" ^ system ])
              in
              lacks env "program is ill-typed" out "ill-typed";
              has env
                (name ^ " outputs everything")
                out
                (String.concat ".*" expected)))
        [ "bap:stubbed-executor"; "bap:legacy-main"; "bap:unicorn-executor" ])
    [
      "arm-linux-gnueabi-echo";
      "x86-linux-gnu-echo";
      "x86_64-linux-gnu-echo";
      "riscv64-linux-gnu-echo";
      "aarch64-linux-gnu-echo";
      "mips-linux-gnu-echo";
      "mips64-linux-gnueabi-echo";
      "powerpc32-linux-gnu-echo";
    ]

(* computes the CRC of the bytes and checks the printed value *)
let crc ?(timeout = 300.) data name bin system expected =
  case name (fun env ->
      let out =
        bap ~timeout env
          [
            path data ("bin/" ^ bin); "--passes=run"; "--run-systems=" ^ system;
          ]
      in
      contains env "prints the CRC" out expected)

(* the loops of a million iterations take hours in the interpreter, so
   the code must run in Unicorn; the Thumb code calls the PLT with blx,
   which switches to the A32 code at the word-aligned address *)
let unicorn data =
  List.map
    (fun bin ->
      crc data ("run/unicorn/" ^ bin) bin "bap:unicorn-executor" "1635920155")
    [ "x86_64-linux-gnu-crc-loop"; "arm-linux-gnueabihf-thumb-crc-loop" ]
  (* the LSE atomics of ARMv8.1 and the exclusive pair, which the default
     CPU of Unicorn, ARMv8.0, doesn't have, and which the interpreter
     lifts, see lse-crc.c *)
  @ List.map
      (fun system ->
        let bin = "aarch64-linux-gnu-lse-crc" in
        crc data (Printf.sprintf "run/%s/%s" system bin) bin system "1489580789")
      [ "bap:stubbed-executor"; "bap:legacy-main"; "bap:unicorn-executor" ]
  @ List.map
      (fun system ->
        let bin = "arm-linux-gnueabihf-thumb-crc" in
        crc data (Printf.sprintf "run/%s/%s" system bin) bin system "1489580789")
      [ "bap:stubbed-executor"; "bap:legacy-main"; "bap:unicorn-executor" ]

(* the write system calls of Linux, which Primus Lisp doesn't model, so
   the cases define the intrinsics of the system calls, in the directory
   of the program, with its syscalls.lisp *)
let syscalls bin = input ("syscalls/" ^ bin)

let syscall data =
  List.concat_map
    (fun bin ->
      List.map
        (fun system ->
          case (Printf.sprintf "run/syscall/%s/%s" system bin) (fun env ->
              let out =
                bap env
                  [
                    path data ("bin/" ^ bin);
                    "--passes=run";
                    "--run-systems=" ^ system;
                    "--primus-lisp-add=" ^ syscalls bin;
                    "--primus-lisp-load=syscalls";
                  ]
              in
              contains env "prints the CRC" out "1489580789"))
        [ "bap:stubbed-executor"; "bap:unicorn-executor" ])
    [ "x86_64-linux-gnu-syscall-crc"; "aarch64-linux-gnu-svc-crc" ]

(* a program that never ends is terminated after the time in Unicorn *)
let timeout data =
  [
    case "run/unicorn/timeout" (fun env ->
        let out =
          bap ~timeout:120. env
            [
              path data "bin/x86_64-linux-gnu-forever";
              "--passes=run";
              "--run-systems=bap:unicorn-executor";
              "--primus-unicorn-timeout=1";
            ]
        in
        check env "terminates" (out.status = Exited 0);
        contains env "prints A" out "A");
  ]

(* without the stubs of posix, strchr is not defined, and the machine
   stops at its call, as the interpreter does: the stub of PLT, which
   jumps back to the trampoline in Unicorn, is interpreted instead of
   calling itself forever, the trampolines stop Unicorn on RISC-V, where
   the zeros are invalid, and on MIPS, whose slot of GOT is zero, the
   jump to zero faults, instead of ending the run *)
let unresolved data =
  List.map
    (fun (bin, checks) ->
      case ("run/unicorn/unresolved/" ^ bin) (fun env ->
          let out =
            bap ~timeout:60. env
              [
                path data ("bin/" ^ bin);
                "--passes=run";
                "--run-systems=bap:unicorn-executor";
                "--primus-lisp-load=stdio";
                "--primus-print-observations=call,exception";
              ]
          in
          check env "terminates" (out.status = Exited 0);
          sequence env out checks))
    [
      ( "x86_64-linux-gnu-echo",
        [
          ("calls strchr", "\\(call \\(strchr");
          ("doesn't resolve it", "unbound function");
        ] );
      ( "riscv64-linux-gnu-echo",
        [
          ("calls strchr", "\\(call \\(strchr");
          ("doesn't resolve it", "unbound function");
        ] );
      (* the global entries of the GOT of MIPS are resolved by the names
         of their functions, as the slots of the other targets are *)
      ( "mips-linux-gnu-echo",
        [
          ("calls strchr", "\\(call \\(strchr");
          ("doesn't resolve it", "unbound function");
        ] );
    ]

(* bap:terminating-unicorn-executor limits the code that Primus runs,
   e.g., the Lisp stubs, which a small limit stops before they print *)
let limit data =
  List.map
    (fun (n, prints) ->
      case (Printf.sprintf "run/unicorn/limit/%d" n) (fun env ->
          let out =
            bap ~timeout:60. env
              [
                path data "bin/x86_64-linux-gnu-echo";
                "--run-argv=hello,cruel,world";
                "--passes=run";
                "--run-systems=bap:terminating-unicorn-executor";
                Printf.sprintf "--primus-limit-max-length=%d" n;
              ]
          in
          check env "terminates" (out.status = Exited 0);
          if prints then contains env "prints everything" out "course"
          else lacks env "stops before it prints" out "hello"))
    [ (100, false); (1_000_000, true) ]

(* the primitives of Primus Lisp for debugging, in the advice of strcpy,
   which echo calls for its argument, in the debug.lisp of the directory
   of the case *)
let debugging data =
  let run env system lisp args =
    bap ~timeout:120. env
      ([
         path data "bin/x86_64-linux-gnu-echo";
         "--run-argv=hello";
         "--passes=run";
         "--run-systems=" ^ system;
         "--primus-lisp-add=" ^ input ("lisp/" ^ lisp);
         "--primus-lisp-load=posix,debug";
         "--primus-lisp-type-check";
       ]
      @ args)
  in
  List.concat_map
    (fun system ->
      [
        case ("lisp/dump-memory-region/" ^ system) (fun env ->
            let out =
              run env system "dump-memory-region"
                [ "--primus-print-observations=lisp-message" ]
            in
            lacks env "well-typed" out "ill-typed";
            sequence env out
              [
                ("dumps the bytes", "0x50000000: (41 ){16}\\|A{16}\\|");
                ("protects the bytes", "0x50000010: (-- ){16}");
                ("unmapped bytes", "0x50000020: \\?\\? \\?\\? +\\|\\.\\.\\|");
                ("continues", "hello");
              ]);
        case ("lisp/bap-exit/" ^ system) (fun env ->
            let obs = file env "observations" in
            let out =
              run env system "bap-exit"
                [
                  "--primus-print-observations=lisp-message";
                  "--primus-print-output=" ^ obs;
                ]
            in
            check env "exits bap with the code" (out.status = Exited 7);
            let text = In_channel.with_open_bin obs In_channel.input_all in
            contains env "flushes the observations" { out with text }
              "bap exits with 7");
      ])
    [ "bap:stubbed-executor"; "bap:unicorn-executor" ]

(* the cached Lisp program is of the files, that it was loaded from, so
   the changed file is loaded anew, see Bap_primus_lisp_cache *)
let lisp_cache data =
  [
    case "lisp/cache" (fun env ->
        let feature = file env "lisp" and cache = file env "lisp-cache" in
        Sys.mkdir feature 0o755;
        let probe version =
          ignore
            (write env "lisp/probe.lisp"
               (Printf.sprintf "(defmethod init () (msg \"probe %s\"))\n"
                  version))
        in
        let run () =
          bap env
            ~unset:[ "BAP_PRIMUS_LISP_CACHE" ]
            ~env:[ ("BAP_PRIMUS_LISP_CACHE", cache) ]
            [
              path data "bin/x86_64-linux-gnu-echo";
              "--passes=run";
              "--primus-lisp-add=" ^ feature;
              "--primus-lisp-load=probe";
              "--primus-print-observations=lisp-message";
            ]
        in
        let cached kind =
          Sys.file_exists cache
          && Array.exists
               (String.starts_with ~prefix:(kind ^ "-"))
               (Sys.readdir cache)
        in
        probe "v1";
        contains env "loads the program" (run ()) "probe v1";
        check env "caches the source" (cached "source");
        check env "caches the types" (cached "types");
        contains env "loads the cached program" (run ()) "probe v1";
        probe "v2";
        contains env "loads the changed file" (run ()) "probe v2");
  ]

(* the debugger stops the machines at the breakpoints and runs the
   commands of a file, the same in the interpreter and in Unicorn *)
let debugger data =
  let run env system bin commands args =
    bap ~timeout:120. env
      ([
         path data ("bin/" ^ bin);
         "--passes=run";
         "--run-systems=" ^ system;
         "--run-components=bap:debugger";
         "--primus-debugger-commands=" ^ commands;
       ]
      @ args)
  in
  case "debugger/bap:unicorn-executor/x86_64-linux-gnu-crc-loop" (fun env ->
      let out =
        run env "bap:unicorn-executor" "x86_64-linux-gnu-crc-loop"
          (input "debugger/crc-loop/commands")
          [ "--primus-debugger-break=0x4004c0" ]
      in
      sequence env out
        [
          ("stops at the breakpoint", "stopped at 0x4004c0");
          ("shows the register", "RAX = 0x9E7DD6E4");
          ("steps", "stopped at 0x4004c2");
          ("steps again", "stopped at 0x4004c7");
          ("prints the CRC of zero", "4294967295");
        ])
  :: List.map
       (fun system ->
         case
           ("debugger/" ^ system ^ "/x86_64-linux-gnu-echo")
           (fun env ->
             let out =
               run env system "x86_64-linux-gnu-echo"
                 (input "debugger/echo/commands")
                 [
                   "--run-argv=hello";
                   "--primus-debugger-break=print_endline";
                   "--primus-lisp-add=" ^ input "debugger/echo";
                   "--primus-lisp-load=posix,helpers";
                 ]
             in
             sequence env out
               [
                 ("stops at the subroutine", "stopped at 0x4006ed");
                 ("calls the Lisp function", "\\(bap\\) call arg-length\n5\n");
                 ("steps", "stopped at 0x4006ee");
                 ("continues", "hello\nwe\n");
               ];
             lacks env "deletes the breakpoint" out
               "stopped at 0x4006ed.*stopped at 0x4006ed"))
       [ "bap:stubbed-executor"; "bap:unicorn-executor" ]

(* bap script compiles the OCaml scripts, which start bap with their
   options, and use its API, e.g., to add a Primus component *)
let scripts data =
  let crc = path data "bin/x86_64-linux-gnu-crc-loop" in
  let script env file = bap ~timeout:300. env [ "script"; file; crc ] in
  [
    case "script/run" (fun env ->
        let out = script env (input "script/run.ml") in
        check env "exits" (out.status = Exited 0);
        contains env "runs the program" out "1635920155");
    (* the symbols of the file, that the user provides, are the
       subroutines of the bare program too, e.g., of the stubs of the
       PLT, which have no symbols in the file *)
    case "script/bare/read-symbols" (fun env ->
        let out =
          bap ~timeout:300. env
            ~env:
              [
                ("BAP_READ_SYMBOLS_FROM", path data "data/x86_64-elf_so.symbols");
              ]
            [
              "script";
              input "script/bare/read-symbols.ml";
              path data "dyn/x86_64-elf_so";
            ]
        in
        check env "exits" (out.status = Exited 0);
        contains env "names the stub of the PLT" out "bar 0x4A0";
        contains env "has the symbols of the file" out "foo 0x59A");
    case "script/primus" (fun env ->
        let out = script env (input "script/primus.ml") in
        lacks env "loads the plugins" out "Failed to load";
        sequence env out
          [ ("stops", "RAX = 9e7dd6e4"); ("runs the program", "1635920155") ]);
    (* the machines take Unicorn from each other, while their bytes are
       in Unicorn, see Primus.Memory.Backing, and print the same, except
       the argument, that one of them changes, while its pages are
       parked *)
    case "script/unicorn/fork" (fun env ->
        let out =
          bap ~timeout:300. env
            [
              "script";
              input "script/unicorn/fork.ml";
              path data "bin/x86_64-linux-gnu-echo";
            ]
        in
        check env "exits" (out.status = Exited 0);
        sequence env out
          [
            ("forks the machine", "helllloo");
            ("switches the machines", "ccrruueell");
            ("keeps the stores of the parked machine", "(wW|Ww)oorrlldd");
            ("runs both machines to the end", "ccoouurrssee");
          ]);
    (* the libraries, that the script requires, are loaded after the
       plugins, as they may use the libraries of the plugins, whose options
       would be another plugin's otherwise *)
    case "script/require/plugin-options" (fun env ->
        let out =
          bap ~timeout:300. env
            ~env:
              [
                ( "BAP_PRIMUS_LISP_CHANNEL_REDIRECT",
                  "<stdin>:" ^ input "stdin/abc-abc" );
              ]
            [
              "script";
              input "script/require/plugin-options.ml";
              path data "bin/x86_64-linux-gnu-symexec-crc32";
            ]
        in
        contains env "reads the redirected input" out "access granted");
    case "script/error" (fun env ->
        let out = script env (input "script/error/script.ml") in
        check env "fails" (out.status = Exited 1);
        has env "tells the line of the script" out "script\\.ml\", line 2");
  ]

(* the bare projects of the scripts, which are not disassembled, run in
   Unicorn as the disassembled ones: from their entry points, with the
   functions in the Thumb encoding from the symbol table, and the system
   calls lifted on demand *)
let bare data =
  let run env ?(lisp = []) bin =
    bap ~timeout:300. env
      ([
         "script"; input "script/unicorn/bare/run.ml"; path data ("bin/" ^ bin);
       ]
      @ lisp)
  in
  [
    case "script/unicorn/bare/x86_64-linux-gnu-echo" (fun env ->
        let out = run env "x86_64-linux-gnu-echo" in
        sequence env out
          [ ("prints the arguments", "hello"); ("ends", "course") ]);
    case "script/unicorn/bare/arm-linux-gnueabihf-thumb-crc" (fun env ->
        let out = run env "arm-linux-gnueabihf-thumb-crc" in
        contains env "prints the CRC" out "1489580789");
    case "script/unicorn/bare/aarch64-linux-gnu-svc-crc" (fun env ->
        let out =
          run env "aarch64-linux-gnu-svc-crc"
            ~lisp:[ syscalls "aarch64-linux-gnu-svc-crc" ]
        in
        contains env "prints the CRC" out "1489580789");
    case "script/unicorn/bare/mips-linux-gnu-echo" (fun env ->
        let out = run env "mips-linux-gnu-echo" in
        sequence env out
          [ ("prints the arguments", "hello"); ("ends", "course") ]);
    case "script/unicorn/bare/x86_64-linux-gnu-syscall-crc" (fun env ->
        let out =
          run env "x86_64-linux-gnu-syscall-crc"
            ~lisp:[ syscalls "x86_64-linux-gnu-syscall-crc" ]
        in
        contains env "prints the CRC" out "1489580789");
    (* each system lifts the system calls in its own knowledge, with the
       semantics, that the process loads once *)
    case "script/unicorn/bare/twice/x86_64-linux-gnu-syscall-crc" (fun env ->
        let out =
          bap ~timeout:300. env
            [
              "script";
              input "script/unicorn/bare/twice.ml";
              path data "bin/x86_64-linux-gnu-syscall-crc";
              syscalls "x86_64-linux-gnu-syscall-crc";
            ]
        in
        check env "prints the CRC twice" (count out "1489580789" = 2));
  ]

(* the scripts run the programs with Bap_emu, pause them, see and change
   their registers and memory, hook their instructions, stores and calls,
   and restore their snapshots *)
let emu data =
  (* the arguments of the scripts are the program, and the input, that
     some of them redirect the standard input to *)
  let script ?(args = []) env bin file =
    bap ~timeout:300. env ([ "script"; file; path data ("bin/" ^ bin) ] @ args)
  in
  [
    case "emu/x86_64-linux-gnu-echo/main" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo" (input "emu/echo/main.ml")
        in
        sequence env out
          [
            ("pauses at the entry", "paused at the entry 400600");
            ("runs until main", "paused at main 40076b, argc = 4");
            ("reads the memory", "argv\\[1\\] = hello");
            ("writes the memory", "HELLO");
            ("replaces the calls", "crue\nword");
            ("exits", "exited with 0 after [0-9]+ stores");
          ]);
    case "emu/x86_64-linux-gnu-echo/step" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo" (input "emu/echo/step.ml")
        in
        sequence env out
          [
            ("steps", "paused at 400602\npaused at 400605\npaused at 400606");
            ("stops in a hook", "paused at 400733");
            ("replaces a function of the program", "\nwe\n");
            ("calls it", "print_endline was called 11 times");
          ]);
    (* the hook, that stops the program, and the address, at which it
       runs until, don't stop it again, when it continues from there,
       but when the code returns there, after Unicorn stopped elsewhere,
       e.g., at a stub *)
    case "emu/x86_64-linux-gnu-echo/stop" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo" (input "emu/echo/stop.ml")
        in
        sequence env out
          [
            ("stops in each iteration", "paused at 40080b 40080b 40080b, exited");
            ( "runs until each iteration",
              "paused at 400749 400749 400749 400749 400749 400749 400749 \
               400749 400749 400749 400749, exited" );
          ]);
    (* the patched code stays, after the snapshot forks the machine, and
       after it is restored, which Bap_emu.write_direct doesn't guarantee *)
    (* the script reads and writes the state of the machine in Primus *)
    case "emu/x86_64-linux-gnu-echo/primus" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo" (input "emu/echo/primus.ml")
        in
        contains env "reads and writes the registers" out
          "argc 2:64u in Primus, 7 in Unicorn");
    (* the script taints the input, which the code in Unicorn uses, and
       sees the jumps, that it taints, as the Lisp does, see taint/ *)
    case "emu/x86_64-linux-gnu-symexec-crc32/taint" (fun env ->
        let out =
          script env "x86_64-linux-gnu-symexec-crc32"
            ~args:[ input "stdin/abc-abd" ]
            (input "emu/crc32/taint.ml")
        in
        contains env "taints the buffer, not RAX" out "buf1 input, RAX \n";
        contains env "sees the tainted jumps" out
          "jumps: 752:input 752:input 752:input 752:input 7b8:input 752:input \
           752:input 752:input 752:input 7b8:input 83b:input");
    (* the scripts make the registers and the memory symbolic, and the
       solver finds the inputs, that flip the branches *)
    case "emu/x86_64-linux-gnu-symexec-guess/symbolic" (fun env ->
        let out =
          script env "x86_64-linux-gnu-symexec-guess"
            ~args:[ input "stdin/Z" ]
            (input "emu/guess/symbolic.ml")
        in
        contains env "makes RAX symbolic" out "RAX RAX, RBX -\n";
        contains env "flips the branch" out "branch 696 true flips with RAX=41");
    case "emu/x86_64-linux-gnu-symexec-crc32/symbolic" (fun env ->
        let out =
          script env "x86_64-linux-gnu-symexec-crc32"
            ~args:[ input "stdin/abc-abd" ]
            (input "emu/crc32/symbolic.ml")
        in
        contains env "sees the symbolic branches" out
          "branches: 7b6 7b6 7b6 7b6 82d\n";
        contains env "finds the collision of the CRC" out "collision: abd\n");
    (* the checkpoints keep the taint and the symbolic values, e.g., of the
       buffer, which the program, that continues from them, uses *)
    case "emu/x86_64-linux-gnu-symexec-crc32/checkpoint-taint" (fun env ->
        let saved =
          script env "x86_64-linux-gnu-symexec-crc32"
            ~args:[ input "stdin/abc-abd" ]
            (input "emu/crc32/checkpoint-taint/save.ml")
        in
        contains env "saves" saved "saved";
        let out =
          script env "x86_64-linux-gnu-symexec-crc32"
            (input "emu/crc32/checkpoint-taint/restore.ml")
        in
        contains env "restores the taint" out "buf1 input\n";
        contains env "sees the tainted jumps" out
          "jumps: 752:input 752:input 752:input 752:input 7b8:input 752:input \
           752:input 752:input 752:input 7b8:input 83b:input");
    case "emu/x86_64-linux-gnu-symexec-crc32/checkpoint-symbolic" (fun env ->
        let saved =
          script env "x86_64-linux-gnu-symexec-crc32"
            ~args:[ input "stdin/abc-abd" ]
            (input "emu/crc32/checkpoint-symbolic/save.ml")
        in
        contains env "saves" saved "saved";
        let out =
          script env "x86_64-linux-gnu-symexec-crc32"
            (input "emu/crc32/checkpoint-symbolic/restore.ml")
        in
        contains env "sees the symbolic branches" out
          "branches: 7b6 7b6 7b6 7b6 82d\n";
        contains env "finds the collision of the CRC" out "collision: abd\n");
    case "emu/x86_64-linux-gnu-echo/patch" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo" (input "emu/echo/patch.ml")
        in
        sequence env out
          [
            ("runs the patched code", "hello\\+");
            ("exits", "exited");
            ("runs it after the restore", "hello\\+");
            ("exits again", "exited");
          ]);
    case "emu/x86_64-linux-gnu-echo/snapshot" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo" (input "emu/echo/snapshot.ml")
        in
        sequence env out
          [
            ( "takes the snapshot",
              "snapshot at 40076b, RDI = 2, argv\\[1\\] = hello" );
            ("runs", "\nhello\n.*exited 0");
            ( "restores the registers and the memory",
              "restored at 40076b, RDI = 2, argv\\[1\\] = hello" );
            ("runs the changed program", "\nWORLD\n.*exited 0");
            ("restores again", "restored again, RDI = 2, argv\\[1\\] = hello");
            ( "pauses the restored program",
              "paused at 400733\n.*\nhello\n.*exited 0" );
          ]);
    (* the checkpoint keeps the memory, that the script changed, and the
       names, that it gave, which another run of bap loads *)
    case "emu/x86_64-linux-gnu-echo/checkpoint" (fun env ->
        let saved =
          script env "x86_64-linux-gnu-echo"
            (input "emu/echo/checkpoint/save.ml")
        in
        sequence env saved
          [
            ("saves", "saved at 40076b, say at 4006ed");
            ("reports the error", "can't save");
            ("continues", "HELLO\ncruel\n.*exited 0");
          ];
        let restored =
          script env "x86_64-linux-gnu-echo"
            (input "emu/echo/checkpoint/restore.ml")
        in
        sequence env restored
          [
            ("restores", "restored at 40076b, RDI = 3");
            ("names the function", "say at 4006ed");
            ("runs the changed memory", "HELLO\ncruel\n");
            (* the run of main returns to the Lisp stub of
               __libc_start_main, which the checkpoint completes, as it
               exits with the result of main *)
            ("hooks the name", "exited 0, say was called 11 times");
          ]);
    (* the code of the function, that a Lisp stub replaced, runs again,
       e.g., as the script patched it, also from the checkpoint *)
    case "emu/x86_64-linux-gnu-echo/unstub" (fun env ->
        let run file =
          script env "x86_64-linux-gnu-echo"
            ~args:[ input "emu/echo/unstub" ]
            file
        in
        let out = run (input "emu/echo/unstub/stubbed.ml") in
        sequence env out
          [
            ("pauses", "paused at 40076b");
            ("runs the stub", "== stubbed\nexited 0");
            ("checks the function", "putchar is external");
            ( "runs the patched code",
              "== unstubbed\n[^\n]*\\+hello\\+we\\+.*exited 0" );
          ];
        let out = run (input "emu/echo/unstub/restored.ml") in
        has env "runs the patched code of the checkpoint" out
          "== restored\n[^\n]*\\+hello\\+we\\+.*exited 0");
    (* the checkpoint keeps the channels of Lisp, e.g., the input, that
       the program read partly, and is of its program *)
    case "emu/x86_64-linux-gnu-symexec-crc32/checkpoint" (fun env ->
        let saved =
          script env "x86_64-linux-gnu-symexec-crc32"
            ~args:[ input "stdin/abc-abd" ]
            (input "emu/crc32/checkpoint/save.ml")
        in
        sequence env saved
          [ ("reads the first line", "buf1 \"abc\\\\n\""); ("saves", "saved") ];
        let restored =
          script env "x86_64-linux-gnu-symexec-crc32"
            (input "emu/crc32/checkpoint/restore.ml")
        in
        contains env "reads the rest of the input" restored "buf2 \"abd\\n\"";
        let other =
          script env "x86_64-linux-gnu-echo"
            (input "emu/crc32/checkpoint/other.ml")
        in
        contains env "is of its program" other "is of another program");
    case "emu/arm-linux-gnueabihf-thumb-crc" (fun env ->
        let out =
          script env "arm-linux-gnueabihf-thumb-crc" (input "emu/thumb-crc.ml")
        in
        sequence env out
          [
            ("steps the Thumb code", "steps: 202df 202e1 202e3");
            ("prints the CRC", "1489580789");
            ("exits", "exited 0");
          ]);
    (* the BIR of an instruction, lifted on demand from the bytes, that
       the program has now, also in a hook, after the patch, of the Thumb code,
       by the lower bit of its address, and of the code, that the program
       writes *)
    case "emu/bir" (fun env ->
        let out =
          bap ~timeout:300. env
            [
              "script";
              input "emu/bir.ml";
              path data "bin/x86_64-linux-gnu-echo";
              path data "bin/arm-linux-gnueabihf-thumb-crc";
              path data "bin/x86_64-linux-gnu-mprotect";
            ]
        in
        sequence env out
          [
            ("lifts the entry", "400600: 2 bytes\n");
            ("lifts in a hook", "hook 400602: 3 bytes\n.*R9 := RDX\n");
            ("lifts the push of main", "40076b: 1 bytes\n.*RSP := RSP - 8");
            ("lifts the code", "400727: 5 bytes\n.*RDI := 0xA\n");
            ("lifts the patched code", "400727: 5 bytes\n.*RDI := 0x2B\n");
            ("lifts the Thumb code", "202dd: 2 bytes\n.*<- LR");
            ("lifts the unwritten code", "unwritten 405000: 2 bytes\n");
            ( "lifts the written code in a hook",
              "written hook 405000: 5 bytes\n.*RAX := 0x2A\n" );
            ( "lifts the written code",
              "written 405000: 5 bytes\n.*RAX := 0x2A\n" );
          ]);
    (* the code, that ran, and that memcpy, a native function, rewrites,
       runs anew, as Unicorn translates it anew, also after the store of
       the program *)
    case "emu/rewrite" (fun env ->
        let out =
          bap env
            [
              "script";
              input "emu/rewrite.ml";
              path data "bin/x86_64-linux-gnu-rewrite";
            ]
        in
        sequence env out
          [
            ("runs the written code", "returns 42\n");
            ("runs the code, that memcpy rewrote", "returns 7\n");
            ("runs the code, that the store rewrote", "returns 9\n");
            ("exits with the result of main", "exited 7\n");
          ]);
    (* the code, that is hostile to the JIT of the lifted engine, runs in
       it, as in Unicorn, see emu/hostile.ml, e.g., the store, whose
       address wraps around, which crashed the runtime of the blocks *)
    case "emu/hostile" (fun env ->
        let out =
          bap env
            [
              "script";
              input "emu/hostile.ml";
              path data "bin/x86_64-linux-gnu-echo";
            ]
        in
        sequence env out
          (List.concat_map
             (fun engine ->
               let line s = Printf.sprintf "%s: %s\n" engine s in
               [
                 ( "runs the loop of the string instruction",
                   line "rep paused, rdi \\+16, \"ZZZZZZZZZZZZZZZZ>\"" );
                 ("runs the patched code", line "patch paused, ebx 9500");
                 ( "faults on the wrapped store",
                   line "wrap paused, Segmentation fault at 0xFFFFFFFFFFFFFFFF"
                 );
               ])
             [ "unicorn"; "lifted" ]));
    (* the native traces of the instructions, and of the blocks, whose
       instructions are the same, and the backward slice, by both, of the
       result of main, through the stack, without the noise *)
    case "emu/trace" (fun env ->
        let out =
          bap env
            [
              "script";
              input "emu/trace.ml";
              path data "bin/x86_64-linux-gnu-crc-loop";
              path data "bin/x86_64-linux-gnu-slice";
              file env "pcs";
            ]
        in
        let slice =
          "40044a 400451 400454 400456 400458 40045a 400466 40046d 400470 \
           400473 400475 400488 40048b 40048d 400490\n"
        in
        sequence env out
          [
            ("counts", "instructions 71000263, blocks 9000049\n");
            ("expands the blocks", "the same: true, the last is 400589\n");
            ("saves", "saved 1000, 1000 lines, the last is 400589\n");
            ("slices the instructions", "slice of instructions: " ^ slice);
            ("has the gap", "gap at main: true, complete: false\n");
            ("slices the blocks", "slice of blocks: " ^ slice);
            ("has the gap of the blocks", "gap at main: true, complete: false\n");
          ]);
    (* the slices of the odd cases of slice-weird.c, the partial
       registers and bytes, the conditional moves and exchanges, the
       repeated moves, the recursion, the code, that patches itself, in
       the segment, that is writable and executable, whose slots are of
       GOT, the stubs, the hooks and the script, that write, and the
       rings, that lose the accesses, see the comments of the script *)
    case "emu/slice" (fun env ->
        let out =
          bap env
            [
              "script";
              input "emu/slice.ml";
              path data "bin/x86_64-linux-gnu-slice-weird";
            ]
        in
        golden env "emu/slice.txt" out.text);
    (* the slices of the odd cases of ARM, of arm-slice-weird.c, in A32 and
       in Thumb, whose modes the traces record, the conditional ones, the
       IT blocks, the loads and stores of multiple registers, by their
       accesses, VFP, which Unicorn enables, the stubs, and the hooks *)
    case "emu/arm-slice" (fun env ->
        let out =
          bap env
            [
              "script";
              input "emu/slice.ml";
              path data "bin/arm-linux-gnueabihf-slice-weird";
              "arm";
            ]
        in
        golden env "emu/arm-slice.txt" out.text);
    (* the emulators run side by side, each in its own engine, also of
       another target, with their own registers, memory, names and
       hooks *)
    case "emu/side-by-side" (fun env ->
        let out =
          bap ~timeout:300. env
            [
              "script";
              input "emu/side-by-side.ml";
              path data "bin/x86_64-linux-gnu-echo";
              path data "bin/arm-linux-gnueabihf-thumb-crc";
            ]
        in
        sequence env out
          [
            ("pauses a", "a paused at 40076b");
            ("pauses c", "c paused at 40076b");
            ("has the registers of each", "argc: a 2, c 3");
            ("has the names of each", "names: a true, c false");
            ("has the snapshots of each", "the snapshot of a is not of c");
            ( "steps them in turns",
              "steps: 40076c/202df/40076c 40076f/202e1/40076f \
               400771/202e3/400771" );
            ("runs b", "== b\n.*1489580789.*b exited 0");
            ("runs c", "== c\n.*\nworld\nagain\n.*c exited 0");
            ("runs a with its memory", "== a\n.*\nHELLO\n.*a exited 0");
            ("hooks the calls of each", "print_endline: a 10, c 11");
            ("has the knowledge of each", "knowledge: a true, b true");
          ]);
  ]

(* the observers of Lisp see the instructions, the loads and the stores
   of the code, which runs in Unicorn, as they see those of the
   interpreter, except the loads, which the semantics of x86 repeat *)
(* the counts include the return address, that invoke-subroutine stores
   for main, and that its ret loads, and, in Unicorn, the self pointer of
   the thread control block *)
let observations data =
  let run env system =
    bap env
      [
        path data "bin/x86_64-linux-gnu-echo";
        "--passes=run";
        "--run-argv=echo,hello";
        "--run-systems=" ^ system;
        "--primus-lisp-add=" ^ input "observations";
        "--primus-lisp-load=posix,counts";
        "--primus-print-observations=lisp-message";
      ]
  in
  [
    case "run/unicorn/observations" (fun env ->
        let out = run env "bap:unicorn-executor" in
        contains env "sees the events" out "pcs 0x508 stores 0x88C loads 0xE25");
    case "run/stubbed-executor/observations" (fun env ->
        let out = run env "bap:stubbed-executor" in
        contains env "sees the events" out "pcs 0x507 stores 0x873 loads 0x11F1");
  ]

(* the taint of the input, which Lisp introduces, propagates through
   the code, that uses it, which Primus interprets, while the rest runs
   in Unicorn, so the observers see the same tainted jumps, i.e., of
   the loop of the CRC, which ends after the 4 bytes of each line, and
   of the comparison of the CRCs *)
let unicorn_taint data =
  let run env system =
    let stdin = input "stdin/abc-abd" in
    bap env
      [
        path data "bin/x86_64-linux-gnu-symexec-crc32";
        "--passes=run";
        "--run-systems=" ^ system;
        "--primus-lisp-channel-redirect=<stdin>:" ^ stdin;
        "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
        "--primus-lisp-add=" ^ input "taint/unicorn";
        "--primus-lisp-load=posix,tainting";
        "--primus-print-observations=lisp-message";
      ]
  in
  List.map
    (fun system ->
      case
        ("taint/" ^ system ^ "/x86_64-linux-gnu-symexec-crc32")
        (fun env ->
          let out = run env system in
          sequence env out
            [
              ("taints the loop", "tainted jump to 0x752");
              ("taints its exit", "tainted jump to 0x7B8");
              ("taints the comparison", "tainted jump to 0x83B");
              ("counts the tainted jumps", "tainted 0xB jumps");
            ]))
    [ "bap:stubbed-executor"; "bap:unicorn-executor"; "bap:lifted-executor" ]

(* the code, which the program changes, is decoded anew: the first
   tainted jump of the loop of the CRC changes the jne, that continues
   the loop, to je, so the loop ends after the first byte of the first
   line, and before the first byte of the second one, as the bytes are
   not zeros, in Unicorn and in the interpreter *)
let patched_code data =
  let taint system =
    case
      ("taint/" ^ system ^ "/patched-code")
      (fun env ->
        let stdin = input "stdin/abc-abd" in
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-symexec-crc32";
              "--passes=run";
              "--run-systems=" ^ system;
              "--primus-lisp-channel-redirect=<stdin>:" ^ stdin;
              "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
              "--primus-lisp-add=" ^ input "patched-code/taint";
              "--primus-lisp-load=posix,patching";
              "--primus-print-observations=lisp-message";
            ]
        in
        sequence env out
          [
            ("runs the jne", "tainted jump to 0x752");
            ("runs the je", "tainted jump to 0x7B8");
            ("runs the je again", "tainted jump to 0x7B8");
            ("compares the CRCs", "tainted jump to 0x83B");
          ];
        lacks env "runs the jne once" out {|0x752[^\n]*\n[^\n]*0x752|})
  in
  (* the instruction of print_endline, that passes the newline to
     putchar, passes + instead, or the tab on RISC-V, whose short
     instruction has no room for +, which the first call of strlen
     patches, as the call is a stub of Lisp *)
  let echo (arch, sep) system =
    case
      ("run/patched-code/" ^ system ^ "/" ^ arch ^ "-echo")
      (fun env ->
        let out =
          bap env
            ([ path data ("bin/" ^ arch ^ "-echo") ]
            @ api data arch
            @ [
                "--passes=run";
                "--run-argv=echo,hello,world";
                "--run-systems=" ^ system;
                "--primus-lisp-add=" ^ input ("patched-code/echo/" ^ arch);
                "--primus-lisp-load=posix,patching";
              ])
        in
        contains env "prints the patched separator" out
          (String.concat sep [ "echo"; "hello"; "world"; "we" ]))
  in
  let echos =
    [
      ("x86_64-linux-gnu", "+");
      ("x86-linux-gnu", "+");
      ("aarch64-linux-gnu", "+");
      ("arm-linux-gnueabi", "+");
      ("mips-linux-gnu", "+");
      ("mips64-linux-gnueabi", "+");
      ("powerpc32-linux-gnu", "+");
      ("riscv64-linux-gnu", "\t");
    ]
  in
  (* the Thumb code of ARM, whose newline of print is +, after the first
     call of putchar, which also taints the stack in Unicorn, so that
     Primus interprets the Thumb code of print, which reads its buffer
     there, and returns from print, with the Thumb bit *)
  let thumb system =
    case
      ("run/patched-code/" ^ system ^ "/arm-linux-gnueabihf-thumb-crc")
      (fun env ->
        let taint = String.equal system "bap:unicorn-executor" in
        let variant = if taint then "tainted" else "plain" in
        let out =
          bap env
            ([
               path data "bin/arm-linux-gnueabihf-thumb-crc";
               "--passes=run";
               "--run-systems=" ^ system;
               "--primus-lisp-add=" ^ input ("patched-code/thumb/" ^ variant);
               "--primus-lisp-load=posix,patching";
               "--primus-print-observations=lisp-message,exception";
             ]
            @
            if taint then
              [
                "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
              ]
            else [])
        in
        contains env "prints the patched newline" out "1489580789+";
        lacks env "returns from print" out "Segmentation fault";
        if taint then
          contains env "interprets the return of print" out
            "interpreted jump to 0x202FB")
  in
  (* the Thumb and A32 code, that the program writes, which print calls,
     after the first call of putchar, instead of its putchar of the
     newline, through the address with the Thumb bit, which calls the A32
     code by the direct blx, that switches the mode, which returns to the
     Thumb code by bx lr, whose IR clears the Thumb bit, and calls putchar
     with +, all of which Primus interprets in Unicorn, if the code is
     tainted:

     0x8000: push {lr}; blx 0x8100; blx putchar; pop {pc}
     0x8100: mov r0, #0x2b; bx lr
     0x202d0: movw r3, #0x8001; blx r3 *)
  let generated ~taint system =
    let name =
      "run/generated-code/" ^ system
      ^ (if taint then "/tainted/" else "/")
      ^ "arm-linux-gnueabihf-thumb-crc"
    in
    let variant = if taint then "tainted" else "plain" in
    case name (fun env ->
        let out =
          bap env
            ([
               path data "bin/arm-linux-gnueabihf-thumb-crc";
               "--passes=run";
               "--run-systems=" ^ system;
               "--primus-lisp-add=" ^ input ("generated-code/" ^ variant);
               "--primus-lisp-load=posix,generating";
               "--primus-print-observations=lisp-message,exception";
             ]
            @
            if taint then
              [
                "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
              ]
            else [])
        in
        lacks env "returns from print" out "Segmentation fault";
        (* the lifted engine propagates the taint itself, so it runs the
           code of the tainted page, whose jumps the interpreter doesn't
           see, see [Bap_lifted.taint_start] *)
        if taint && not (String.equal system "bap:lifted-executor") then
          (* the messages of the jumps are among the output *)
          sequence env out
            [
              ("prints the CRC", "1489580789");
              ("enters A32 by blx", "interpreted jump to 0x8100");
              ("returns to Thumb by bx lr", "interpreted jump to 0x8007");
              ( "prints + from the generated code",
                {|\+\(lisp-message "interpreted jump to 0x202D7"\)|} );
            ]
        else contains env "prints + from the generated code" out "1489580789+")
  in
  let systems = [ "bap:stubbed-executor"; "bap:unicorn-executor" ] in
  List.map taint (systems @ [ "bap:lifted-executor" ])
  @ List.map thumb systems
  @ List.map (generated ~taint:false) systems
  @ [
      generated ~taint:true "bap:unicorn-executor";
      generated ~taint:true "bap:lifted-executor";
    ]
  @ List.concat_map
      (fun system -> List.map (fun e -> echo e system) echos)
      systems

(* the symbolic executor finds the input, as the code that uses the
   symbolic values is interpreted, and the rest runs in Unicorn *)
let unicorn_symexec data =
  List.map
    (fun name ->
      case ~slow:true ("symexec/bap:unicorn-executor/" ^ name) (fun env ->
          let out =
            bap env ~timeout:120. ~until:"access"
              ((path data ("bin/" ^ name) :: api data name)
              @ [
                  "--passes=run";
                  "--run-systems=bap:unicorn-executor";
                  "--run-components=bap:greedy-scheduler,bap:symbolic-computer,bap:symbolic-path-explorer,bap:symbolic-path-constraints,bap:symbolic-lisp-primitives";
                  "--primus-lisp-load=symbolic-stdio,posix";
                  "--primus-symbolic-executor-cutoff-level=16";
                  "--primus-symbolic-executor-timeout=1000";
                  "--run-in-isolation";
                ])
          in
          match out.status with
          | Stopped -> check env (name ^ " was hacked!") true
          | Exited _ when matches out "access" ->
              check env (name ^ " was hacked!") true
          | _ -> check env (name ^ " withhold the attack.") false))
    (List.concat_map
       (fun target ->
         List.map
           (fun program -> target ^ "-symexec-" ^ program)
           [ "simple"; "input"; "guess" ])
       [
         "x86_64-linux-gnu";
         "aarch64-linux-gnu";
         "arm-linux-gnueabi";
         "mips-linux-gnu";
         "powerpc-linux-gnu";
       ])

(* the scripts stop the machines with Bap_script_debugger, and see and
   change them in their handlers, the same in the interpreter and in
   Unicorn *)
let script_debugger data =
  let script env file args = bap ~timeout:300. env ("script" :: file :: args) in
  case "script/debugger/bap:unicorn-executor/x86_64-linux-gnu-crc-loop"
    (fun env ->
      let out =
        script env
          (input "script/debugger/crc-loop.ml")
          [ path data "bin/x86_64-linux-gnu-crc-loop" ]
      in
      sequence env out
        [
          ("stops", "at 4004c0 RAX = 9e7dd6e4");
          ("steps", "stepped to 4004c2");
          ("prints the CRC of zero", "4294967295");
        ])
    (* the debugger, which stops the machine no more, after the stepping
     is off, without the breakpoints, doesn't make Unicorn stop at every
     instruction, as it observes only the stops, so the loop runs at the
     speed of Unicorn, which it didn't in 20 seconds otherwise; as the
     time measures the speed, the case runs alone, since the other cases,
     that run in parallel, slow it down, e.g., on Windows *)
  :: case ~serial:true "script/debugger/bap:unicorn-executor/stepping-off"
       (fun env ->
         let out =
           bap ~timeout:20. env
             [
               "script";
               input "script/debugger/stepping-off.ml";
               path data "bin/x86_64-linux-gnu-crc-loop";
             ]
         in
         check env "exits" (out.status = Exited 0);
         sequence env out
           [
             ("prints the CRC", "1635920155");
             ("stops while stepping", "stopped 3 times");
           ])
  :: List.map
       (fun system ->
         case
           ("script/debugger/" ^ system ^ "/x86_64-linux-gnu-echo")
           (fun env ->
             let out =
               script env
                 (input "script/debugger/echo.ml")
                 [ system; path data "bin/x86_64-linux-gnu-echo" ]
             in
             contains env "stops at each call" out
               "print_endline was called 9 times"))
       [ "bap:stubbed-executor"; "bap:unicorn-executor" ]

(* the CRC programs save the checkpoint at an instruction of the loop
   that prints the digits, from which another run continues, and the
   run that continues from the checkpoint saves it, when it reaches the
   instruction again, i.e., after the next digit *)
let checkpoint data =
  let unicorn env bin args =
    bap env
      ([
         path data ("bin/" ^ bin);
         "--passes=run";
         "--run-systems=bap:unicorn-executor";
       ]
      @ args)
  in
  let save file at =
    [
      "--primus-unicorn-checkpoint=" ^ file;
      "--primus-unicorn-checkpoint-at=" ^ at;
    ]
  in
  let restore file = [ "--primus-unicorn-restore=" ^ file ] in
  List.map
    (fun (bin, at) ->
      case ("run/unicorn/checkpoint/" ^ bin) (fun env ->
          let file = file env "checkpoint" in
          let out = unicorn env bin (save file at) in
          contains env "prints the CRC" out "1635920155";
          let out = unicorn env bin (restore file) in
          contains env "prints the other digits" out "635920155";
          lacks env "skips the loop" out "1635920155"))
    (* the instructions after the first call of putchar *)
    [
      ("x86_64-linux-gnu-crc-loop", "0x40055b");
      ("arm-linux-gnueabihf-thumb-crc-loop", "0x202d4");
    ]
  @ [
      (* the load of the digit, which faults, as the restored machine
         copies the pages anew *)
      case "run/unicorn/checkpoint/again" (fun env ->
          let bin = "x86_64-linux-gnu-crc-loop" in
          let first = file env "first" and second = file env "second" in
          let _ = unicorn env bin (save first "0x40054c") in
          let out = unicorn env bin (restore first @ save second "0x40054c") in
          contains env "prints the CRC" out "1635920155";
          let out = unicorn env bin (restore second) in
          contains env "prints the other digits" out "635920155";
          lacks env "skips the first digit" out "1635920155");
    ]

(* the program makes its code executable and then read-only with
   mprotect, the interpreter can't run the code that it writes, but
   both executors deny the store to the read-only memory *)
let mprotect data =
  List.map
    (fun system ->
      case ("run/mprotect/" ^ system) (fun env ->
          let out =
            bap env
              [
                path data "bin/x86_64-linux-gnu-mprotect";
                "--passes=run";
                "--run-systems=" ^ system;
                "--primus-print-observations=exception";
              ]
          in
          if String.equal system "bap:unicorn-executor" then
            contains env "runs the code" out "42";
          sequence env out
            [
              ("prints W", "\\bW\\b");
              ("denies the store", "Segmentation fault at 0x405000");
            ];
          lacks env "stops" out "\\bX\\b"))
    [ "bap:stubbed-executor"; "bap:unicorn-executor" ]

(* the code, that patches the instruction after it, in the same block,
   and restores it, runs patched, also in the blocks, that the JIT of
   the lifted engine compiled, see smc.c, whose stores to the code stop
   the block, in both executors *)
let smc data =
  List.map
    (fun system ->
      case ("run/smc/" ^ system) (fun env ->
          let out =
            bap env
              [
                path data "bin/x86_64-linux-gnu-smc";
                "--passes=run";
                "--run-systems=" ^ system;
              ]
          in
          contains env "runs the patched code" out "s 250216 250216"))
    [ "bap:unicorn-executor"; "bap:lifted-executor" ]

(* the taint, that the lifted engine propagates itself, is the one, that
   the interpreter propagates, by the policy of the computations, and of
   the moves, through the moves, the arithmetic, the bytes of the words,
   the copies of the memory, and not the constants, the branches, and the
   values, that the program writes over, see taint-ops.c *)
let taint_ops data =
  let expected = function
    | "exact" ->
        "out: 0=input 1=- 2=- 3=- 4=input 5=input 6=- 7=- 8=- 9=- 10=- 11=- \
         12=- 13=- 14=- 15=- 16=input 17=input 18=input 19=input 20=input \
         21=input 22=input 23=input 24=input 25=- 26=- 27=-\n\
         RDI: input\n\
         RSI: -\n\
         RDX: -\n\
         RCX: -\n"
    | _ ->
        "out: 0=input 1=input 2=- 3=- 4=input 5=input 6=- 7=- 8=input 9=input \
         10=input 11=input 12=input 13=input 14=input 15=input 16=input \
         17=input 18=input 19=input 20=input 21=input 22=input 23=input \
         24=input 25=- 26=input 27=-\n\
         RDI: input\n\
         RSI: input\n\
         RDX: -\n\
         RCX: input\n"
  in
  List.concat_map
    (fun policy ->
      List.map
        (fun (mode, shadow) ->
          case
            ("emu/taint-ops/" ^ policy ^ "/" ^ mode)
            (fun env ->
              let out =
                bap env
                  ~env:[ ("BAP_LIFTED_TAINT", shadow) ]
                  [
                    "script";
                    input "emu/taint-ops/script.ml";
                    policy;
                    path data "bin/x86_64-linux-gnu-taint-ops";
                  ]
              in
              has env "propagates the taint" out (expected policy);
              has env "exits" out "exited\n"))
        [ ("lifted", "true"); ("interpreted", "false") ])
    [ "computation"; "exact" ]

(* the copies of libc, which run natively, while the lifted engine
   propagates the taint, propagate it as their Lisp stubs, see
   taint-natives.c *)
let taint_natives data =
  List.map
    (fun (mode, shadow) ->
      case ("emu/taint-natives/" ^ mode) (fun env ->
          let out =
            bap env
              ~env:[ ("BAP_LIFTED_TAINT", shadow) ]
              [
                "script";
                input "emu/taint-natives/script.ml";
                path data "bin/x86_64-linux-gnu-taint-natives";
              ]
          in
          let tainted n =
            String.concat " "
              (List.init 18 (fun i -> if i < n then "input" else "-"))
          in
          has env "propagates the taint of the copies" out
            (Printf.sprintf "memcpy: %s\nmemset: %s\nstrcpy: %s\nmemmove: %s\n"
               (tainted 9) (tainted 8) (tainted 8) (tainted 4));
          has env "exits" out "abcdefgh 98 8\nexited\n"))
    [ ("lifted", "true"); ("interpreted", "false") ]

(* the hooks of the memory see the same reads and writes of the
   crc-loop in Unicorn and in the lifted engine, whose loop runs compiled,
   as the code, that doesn't access the hooked pages, runs compiled also
   with the hooks, and in time, see emu/hooks/script.ml *)
let memory_hooks data =
  List.map
    (fun engine ->
      case ("emu/hooks/" ^ engine) (fun env ->
          let out =
            bap ~timeout:30. env
              [
                "script";
                input "emu/hooks/script.ml";
                engine;
                path data "bin/x86_64-linux-gnu-crc-loop";
              ]
          in
          has env "sees the accesses" out "reads 26 writes 28\n"))
    [ "unicorn"; "lifted" ]

(* the taint of the bytes of the page of the bss, which are generated,
   when they are read, stays, and the code, that doesn't use the
   tainted values, runs in the engine, without the events of its loads
   and stores, which the observers of the taint don't need, see
   taint-bss.c, so that it ends in time *)
let taint_bss data =
  List.map
    (fun engine ->
      case ("emu/taint-bss/" ^ engine) (fun env ->
          let out =
            bap ~timeout:60. env
              [
                "script";
                input "emu/taint-bss/script.ml";
                engine;
                path data "bin/x86_64-linux-gnu-taint-bss";
              ]
          in
          sequence env out
            [
              ("taints the CRC of buf", "RDX: input\n");
              ("taints the count of its odd bytes", "RCX: input\n");
              ("doesn't taint the other CRC", "RSI: -\n");
              ("exits", "exited\n");
            ]))
    [ "unicorn"; "lifted" ]

(* calloc of Primus Lisp returns the zeros, also in the arena, whose
   values are random, which the engine has, and null, if the size
   overflows, malloc aligns its chunks to 16 bytes, and realloc keeps
   the bytes of the chunk, that it shrinks, see calloc.c *)
let calloc data =
  List.map
    (fun system ->
      case ("run/calloc/" ^ system) (fun env ->
          let out =
            bap env
              [
                path data "bin/x86_64-linux-gnu-calloc";
                "--passes=run";
                "--run-systems=" ^ system;
              ]
          in
          sequence env out
            [
              ("zeroes the memory", "calloc 0 ");
              ("fails on the overflow", "overflow \\(nil\\)");
              ("aligns the chunks", "misaligned 0 ");
              ("keeps the bytes of a shrunk chunk", "realloc 0 7");
            ]))
    [ "bap:stubbed-executor"; "bap:unicorn-executor"; "bap:lifted-executor" ]

(* the stubs of the printf family format the words, that the C ABI
   passes, also on the stack, the streams of libc are the channels of
   Lisp, whether the program refers to them with a copy relocation, or
   through the GOT, as the fortified one does, which calls __printf_chk,
   and the program exits with the result of main *)
let printf_family data =
  let lines =
    [
      "int 42 neg -7 unsigned 3000000000 hex ff HEX 0XFF oct 10\n";
      "long -1234567890123 18446744073709551615 deadbeefcafe char Z str [hi] \
       [   ab] [ab   |] [ab]\n";
      "pad [   12] [12   |] [-0012] [+5] [ 5] [007] [   9] %\n";
      "stack 1 2 3 4 5 6 7 8\n";
      "ptr 0x1234 null (nil) (null)\n";
      "sprintf [s10xyz] 6 snprintf [truncat] 16\n";
    ]
  in
  List.concat_map
    (fun bin ->
      List.map
        (fun system ->
          case
            ("run/" ^ bin ^ "/" ^ system)
            (fun env ->
              let stderr = file env "stderr" in
              let out =
                bap env
                  [
                    path data ("bin/x86_64-linux-gnu-" ^ bin);
                    "--passes=run";
                    "--run-systems=" ^ system;
                    "--primus-lisp-channel-redirect=<stderr>:" ^ stderr;
                    "--primus-print-observations=exited";
                  ]
              in
              List.iter (fun line -> contains env line out line) lines;
              contains env "exits with the result of main" out "(exited 3:";
              lacks env "doesn't print stderr to stdout" out "err 99";
              let err =
                {
                  out with
                  text = In_channel.with_open_bin stderr In_channel.input_all;
                }
              in
              contains env "prints to stderr" err "err 99\n"))
        [ "bap:stubbed-executor"; "bap:unicorn-executor" ])
    [ "printf"; "printf-chk" ]

(* the program maps an anonymous page with mmap, runs the code that it
   writes there, after it makes it executable, and reads from the page,
   after it unmaps it *)
let mmap data =
  [
    case "run/mmap/bap:unicorn-executor" (fun env ->
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-mmap";
              "--passes=run";
              "--primus-lisp-type-check";
              "--run-systems=bap:unicorn-executor";
              "--primus-print-observations=exception";
            ]
        in
        lacks env "well-typed" out "ill-typed";
        sequence env out
          [
            ("runs the code", "\\b42\\b");
            ("unmaps the page", "\\bU\\b");
            ("denies the load", "Segmentation fault at 0x7F0000000000");
          ];
        lacks env "stops" out "\\bX\\b");
    (* the interpreter runs the code, that the program writes, as it is
       in the memory, see Primus.Lift *)
    case "run/mmap/bap:stubbed-executor" (fun env ->
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-mmap";
              "--passes=run";
              "--run-systems=bap:stubbed-executor";
              "--primus-print-observations=exception";
            ]
        in
        sequence env out
          [
            ("runs the code", "\\b42\\b");
            ("unmaps the page", "\\bU\\b");
            ("denies the load", "Segmentation fault at 0x7F0000000000");
          ];
        lacks env "stops" out "\\bX\\b");
    (* the stack is tainted, so the code that the program writes, and
       which returns through it, is interpreted, from its bytes *)
    case "run/mmap/interpreted" (fun env ->
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-mmap";
              "--passes=run";
              "--run-systems=bap:unicorn-executor";
              "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
              "--primus-lisp-add=" ^ input "run/mmap";
              "--primus-lisp-load=posix,stack";
              "--primus-print-observations=exception";
            ]
        in
        lacks env "interprets the code" out "can't interpret";
        sequence env out
          [ ("runs the code", "\\b42\\b"); ("unmaps the page", "\\bU\\b") ]);
  ]

(* the rules of Linux for the pages, see src/pages.c *)
let pages data =
  List.map
    (fun system ->
      case ("run/pages/" ^ system) (fun env ->
          let out =
            bap env
              [
                path data "bin/x86_64-linux-gnu-pages";
                "--passes=run";
                "--run-systems=" ^ system;
                "--primus-print-observations=exception";
              ]
          in
          contains env "returns the errors" out
            "4096\n0\n-1\n22\n-1\n22\n-1\n22\n-1\n19\n0\n0\nW\n";
          contains env "protects the page" out
            "Segmentation fault at 0x7F0000000FA0"))
    [ "bap:stubbed-executor"; "bap:unicorn-executor" ]

let contains_any subs name =
  List.exists
    (fun sub ->
      let n = String.length sub in
      let rec loop i =
        i + n <= String.length name
        && (String.sub name i n = sub || loop (i + 1))
      in
      loop 0)
    subs

(* the binaries of mingw have the most code, so they are the slowest *)
let mingw = contains_any [ "mingw" ]

let taint data =
  let opts =
    [
      "--passes=run";
      "--run-entry-points=all-subroutines";
      "--primus-limit-max-length=4096";
      "--primus-greedy-scheduler";
      "--primus-propagate-taint-from-attributes";
      "--primus-propagate-taint-to-attributes";
      "--primus-lisp-channel-redirect=<stdout>:stdout";
    ]
    @ List.map (fun reg -> "--taint-reg=" ^ reg) [ "ZF"; "A0"; "R1"; "X1" ]
    @ List.map
        (fun attr -> "--print-bir-attr=" ^ attr)
        [ "tainted-reg"; "tainted-regs"; "visited"; "dead" ]
  in
  List.concat_map
    (fun system ->
      files data "bin" (fun name -> String.ends_with ~suffix:"-echo" name)
      |> List.map (fun file ->
          let name =
            Printf.sprintf "taint/%s/%s" system (Filename.basename file)
          in
          case ~slow:(mingw file) name (fun env ->
              (* the legacy main system that explores all paths, as the
                 promiscuous executor does *)
              let systems = input "taint/promiscuous-main.asd" in
              let out =
                bap env
                  ((path data file :: opts) @ api data file
                  @ [
                      "--dump=bir";
                      "--primus-systems-add-path=" ^ systems;
                      "--run-systems=" ^ system;
                    ])
              in
              has env ("introduce in " ^ system) out {|\.tainted-reg|};
              has env ("propagate in " ^ system) out {|\.tainted-regs|};
              has env ("visited in " ^ system) out {|\.visited|};
              (* the code of these binaries isn't reachable from the entries *)
              if not (contains_any [ "android"; "mips"; "w64-mingw" ] file) then
                lacks env "no-dead-code" out {|\.dead|})))
    [ "test:promiscuous-legacy-main"; "bap:reflective-taint-analyzer" ]

(* the symbolic executor finds the input that makes a binary print access *)
let symexec data =
  files data "bin" (fun name -> contains_any [ "-symexec-" ] name)
  |> List.map (fun file ->
      let name = "symexec/" ^ Filename.basename file in
      case ~slow:true name (fun env ->
          let out =
            bap env ~timeout:240. ~until:"access"
              ((path data file :: api data file)
              @ [
                  "--passes=run";
                  "--run-systems=bap:symbolic-executor";
                  "--primus-lisp-load=symbolic-stdio,posix";
                  "--primus-symbolic-executor-cutoff-level=16";
                  (* the solver has 16 ms by default, which the
                     cases, that run in parallel, may exceed, and then
                     bap exits without finding the input *)
                  "--primus-symbolic-executor-timeout=1000";
                  "--run-in-isolation";
                ])
          in
          (* bap may print access and exit, before its output is
             checked, so that it is not stopped *)
          match out.status with
          | Stopped -> check env (file ^ " was hacked!") true
          | Exited _ when matches out "access" ->
              check env (file ^ " was hacked!") true
          | Timeout -> check env (file ^ " run out of time.") false
          | _ -> check env (file ^ " withhold the attack.") false))

(* the signals stop the loop of signal-loop.c, which runs in Unicorn
   without calls, so that their handlers run, e.g., of the script, which
   saves the checkpoint, and the stores, which the loop is in, don't run
   again, as Unicorn continues, see build.cmake of libunicorn; the signals
   are not watched on Windows *)
let emu_signals data =
  let script env file =
    bap ~timeout:300. env
      [
        "script";
        input ("emu/signal/" ^ file);
        path data "bin/x86_64-linux-gnu-signal-loop";
      ]
  in
  let sum = "1080774656\n" in
  if Sys.win32 then []
  else
    [
      case "emu/x86_64-linux-gnu-signal-loop/checkpoint" (fun env ->
          let out = script env "save.ml" in
          sequence env out
            [
              ("pauses in the loop", "paused in the loop\nsaved\n");
              ("continues", sum ^ "exited");
            ];
          let out = script env "restore.ml" in
          has env "continues from the checkpoint" out (sum ^ "exited"));
      case "emu/x86_64-linux-gnu-signal-loop/interrupts" (fun env ->
          let out = script env "interrupts.ml" in
          has env "runs the stores once" out
            (sum ^ "exited, the handler ran while it ran"));
    ]

(* the threads of threads.c, that the system calls of Linux create, which
   are preempted, and wait on the futexes, of threads-weird.c, on the
   targets of Linux, and of threads-win.c, that the functions of Windows
   create, see Primus_unicorn_executor *)
let threads data =
  List.map
    (fun target ->
      let bin = target ^ "-threads" in
      case ("run/unicorn/threads/" ^ bin) (fun env ->
          let out =
            bap ~timeout:300. env
              [
                path data ("bin/" ^ bin);
                "--passes=run";
                "--run-systems=bap:unicorn-executor";
              ]
          in
          check env "exits" (out.status = Exited 0);
          has env "counts the steps of the threads" out "8000\nok\n"))
    [ "x86_64-linux-gnu"; "aarch64-linux-gnu" ]
  @ [
      (* the taint of a register of a thread stays, while the threads
         switch, also in the program, that continues from the checkpoint,
         which keeps the threads *)
      case "emu/x86_64-linux-gnu-threads/checkpoint" (fun env ->
          let script args =
            bap ~timeout:300. env
              ([
                 "script";
                 input "emu/threads/save.ml";
                 path data "bin/x86_64-linux-gnu-threads";
               ]
              @ args)
          in
          let taint out =
            has env "taints R8 of the thread 2" out
              "R8 of the thread 2: input\n";
            lacks env "doesn't taint the other threads" out
              "R8 of the thread [^2]: input";
            has env "finishes the threads" out "8000\nok\nexited"
          in
          let out = script [] in
          sequence env out
            [
              ("taints in the thread 2", "tainted in the thread 2\n");
              ("saves in main", "saved in the thread 1\n");
            ];
          taint out;
          let out = script [ "restore" ] in
          has env "restores in main" out "restored in the thread 1\n";
          taint out);
    ]
  @ List.concat_map
      (fun target ->
        let bin = target ^ "-threads-weird" in
        let lines =
          "taint 22099\n\
           tls ok\n\
           nested 43\n\
           pingpong ok\n\
           errors -11 -110 -38 -38\n\
           many 2400\n\
           orphan\n"
        in
        [
          (* the odd uses of the threads, see threads-weird.c *)
          case ("run/unicorn/threads/" ^ bin) (fun env ->
              let out =
                bap ~timeout:300. env
                  ([
                     path data ("bin/" ^ bin);
                     "--passes=run";
                     "--run-systems=bap:unicorn-executor";
                   ]
                  @ api data bin)
              in
              check env "exits" (out.status = Exited 0);
              has env "runs the odd threads" out lines);
          (* the taint, that goes to a thread through clone, and the
             memory, which is not in Unicorn, as it is tainted, so that
             the futexes and the TIDs are in Primus, and the checkpoints,
             while a thread waits, in a thread, of a restored program,
             and after main exited, see threads-weird/script.ml *)
          case
            ("emu/" ^ bin ^ "/checkpoints")
            (fun env ->
              let script args =
                bap ~timeout:300. env
                  ([
                     "script";
                     input "emu/threads-weird/script.ml";
                     path data ("bin/" ^ bin);
                   ]
                  @ args
                  @
                  if String.starts_with ~prefix:"powerpc" bin then
                    [ "api=" ^ path data "api/powerpc" ]
                  else [])
              in
              let taint out =
                has env "taints through clone and the memory" out
                  "inherited: secret\nmixed: secret\nclean: -\n"
              in
              let exits out =
                has env "exits with the code of the last thread" out
                  "orphan\n\
                   exited 7\n\
                   inherited: secret\n\
                   mixed: secret\n\
                   clean: -\n"
              in
              let out = script [] in
              sequence env out
                [
                  ("saves while the mixer waits", "saved mixer.ckpt\n");
                  ( "runs the thread, that waited",
                    "taint_joined in the thread 1\n" );
                  ("saves in a thread", "pinged in the thread 9\n");
                  ("saves after main exited", "orphaned in the thread 34\n");
                ];
              taint out;
              has env "runs the odd threads" out "many 2400\n";
              exits out;
              let out = script [ "restore"; "mixer.ckpt"; "again.ckpt" ] in
              has env "restores in main" out
                "restored mixer.ckpt in the thread 1\n";
              taint out;
              has env "runs the restored threads" out
                "taint 22099\ntls ok\nnested 43\n";
              has env "saves the restored program" out "saved again.ckpt\n";
              exits out;
              List.iter
                (fun ckpt ->
                  let out = script [ "restore"; ckpt ] in
                  has env "restores in the thread" out
                    ("restored " ^ ckpt ^ " in the thread 9\npingpong ok\n");
                  exits out)
                [ "pingpong.ckpt"; "again.ckpt" ];
              let out = script [ "restore"; "orphan.ckpt" ] in
              has env "restores without main" out
                "restored orphan.ckpt in the thread 34\n";
              exits out);
        ])
      [
        "x86_64-linux-gnu";
        "aarch64-linux-gnu";
        "i686-linux-gnu";
        "arm-linux-gnueabihf";
        "mips-linux-gnu";
        "mips64-linux-gnuabi64";
        "powerpc-linux-gnu";
        "riscv64-linux-gnu";
      ]
  @ List.concat_map
      (fun target ->
        let bin = target ^ "-threads-win" in
        let lines =
          "events ok\n\
           semaphore 3\n\
           condition 155\n\
           address 42\n\
           tls ok\n\
           suspended 11\n\
           timeouts 258 258 0\n\
           exit 5\n\
           orphan\n"
        in
        [
          (* the threads of Windows, and their objects, see
             threads-win.c *)
          case ("run/unicorn/threads/" ^ bin) (fun env ->
              let out =
                bap ~timeout:300. env
                  [
                    path data ("bin/" ^ bin);
                    "--passes=run";
                    "--run-systems=bap:unicorn-executor";
                  ]
              in
              check env "exits" (out.status = Exited 0);
              has env "runs the threads" out ("create 4000 46\n" ^ lines));
          (* the taint, that a thread mixes, in the memory, which is not
             in Unicorn, as it is tainted, so that the objects of
             Windows are in Primus, and the checkpoint, while a thread
             waits on an event, see threads-win/script.ml *)
          case
            ("emu/" ^ bin ^ "/checkpoint")
            (fun env ->
              let script args =
                bap ~timeout:300. env
                  ([
                     "script";
                     input "emu/threads-win/script.ml";
                     path data ("bin/" ^ bin);
                   ]
                  @ args)
              in
              let finishes out =
                has env "finishes the threads" out (lines ^ "exited 7\n");
                has env "taints the mixed seed" out
                  "turns: -\nseed: secret\nmixed: secret\n"
              in
              let out = script [] in
              sequence env out
                [
                  ("pauses in main", "paused in the thread 1\n");
                  ("saves while the thread waits", "saved events.ckpt\n");
                ];
              finishes out;
              let out = script [ "restore" ] in
              has env "restores in main" out "restored in the thread 1\n";
              finishes out);
        ])
      [ "x86_64-pc-windows-msvc"; "i686-pc-windows-msvc" ]

(* the scripts on every target, that the testsuite has the binaries of:
   the symbolic and the tainted registers and memory, the branches and
   their flips, the hooks, the snapshots, and the misuses, e.g., of the
   aliases of the registers, e.g., W0 of AArch64 or V0 of MIPS, which the
   code doesn't read, as it reads their base registers *)
let emu_targets data =
  let api file =
    if String.starts_with ~prefix:"powerpc" file then
      [ path data "api/powerpc" ]
    else []
  in
  let script env file args = bap ~timeout:300. env ("script" :: file :: args) in
  (* the target, the address after getchar returns, the register, that
     holds its result, the base register, that the code reads, and the
     branch on it, see symexec-guess.c *)
  let guesses =
    [
      ("x86_64-linux-gnu", "0x693", "EAX", "RAX", "696");
      ("aarch64-linux-gnu", "0x780", "W0", "R0", "784");
      ("arm-linux-gnueabi", "0x1043c", "R0", "R0", "10444");
      ("mips-linux-gnu", "0x40077c", "V0", "R2", "400788");
      ("powerpc-linux-gnu", "0x100004e4", "R3", "R3", "100004ec");
      ("x86_64-w64-mingw32", "0x401572", "EAX", "RAX", "401575");
      ("i686-w64-mingw32", "0x401543", "EAX", "EAX", "401546");
    ]
  in
  let guess = input "emu/targets/guess.ml" in
  let crc32 = input "emu/targets/crc32.ml" in
  let echo = input "emu/targets/echo.ml" in
  let run = input "emu/targets/run.ml" in
  let echos =
    [
      "x86_64-linux-gnu";
      "x86-linux-gnu";
      "aarch64-linux-gnu";
      "arm-linux-gnueabi";
      "mips-linux-gnu";
      "mips64-linux-gnueabi";
      "powerpc32-linux-gnu";
      "riscv64-linux-gnu";
    ]
  in
  List.concat_map
    (fun (target, until, reg, base, branch) ->
      let file = "bin/" ^ target ^ "-symexec-guess" in
      let run env stdin =
        script env guess
          ([ path data file; input ("stdin/" ^ stdin); until; reg ] @ api target)
      in
      [
        case
          ("emu/" ^ target ^ "-symexec-guess/flip")
          (fun env ->
            let out = run env "Z" in
            sequence env out
              [
                ("the register is concrete", "before: -\n");
                ("rejects the unknown register", "rejects the unknown register");
                ("symbolizes the base register", "after: " ^ base ^ "\n");
                ("solves no constraints", "unsolved: \n");
                ("rejects the symbolization in the hook", "rejects the hook");
                ("exits", "exited 0");
                ( "flips the branch to A",
                  "branch " ^ branch ^ " taken flips with " ^ base ^ "=41\n" );
                ("sees one branch", "branches 1\n");
                ("solves the path", "solved: " ^ base ^ "=");
                ("keeps the formula after the exit", "ended: ");
              ];
            lacks env "the path avoids A" out ("solved: " ^ base ^ "=41\n"));
        case
          ("emu/" ^ target ^ "-symexec-guess/granted")
          (fun env ->
            let out = run env "A" in
            sequence env out
              [
                ("grants the access", "access granted");
                ("exits", "exited 0");
                ( "falls through the branch",
                  "branch " ^ branch ^ " fell flips with " ^ base ^ "=" );
              ];
            lacks env "flips away from A" out "fell flips with [A-Z0-9]+=41\n");
      ])
    guesses
  @ List.map
      (fun target ->
        case ~slow:true
          ("emu/" ^ target ^ "-symexec-crc32/collision")
          (fun env ->
            let stdin = input "stdin/abc-abd" in
            let out =
              script env crc32
                ([ path data ("bin/" ^ target ^ "-symexec-crc32"); stdin ]
                @ api target)
            in
            sequence env out
              [
                ("pauses at crc32", "at crc32: paused after 2 reads");
                ("reads the lines", "buf1 \"abc\\\\n\", buf2 \"abd\\\\n\"");
                ("symbolizes the bytes", "symbolic: SSSS-");
                ("taints the bytes", "tainted: true false");
                ("exits", "exited 0, crc32 called 2 times");
                ( "sees the branches and the jumps",
                  "symbolic branches: true, tainted jumps: true" );
                ("finds the collision of the CRC", "collision \"abd\\\\n\"");
                ("sanitizes the bytes", "sanitized: false");
              ]))
      (List.map (fun (target, _, _, _, _) -> target) guesses)
  @ List.concat_map
      (fun target ->
        let file = path data ("bin/" ^ target ^ "-echo") in
        [
          case
            ("emu/" ^ target ^ "-echo/hooks")
            (fun env ->
              let out = script env echo (file :: api target) in
              sequence env out
                [
                  ("has the registers", "registers: true");
                  ("steps", "step: paused, moved true");
                  ( "has no argument outside of a call",
                    "no argument outside of a call" );
                  ("has no write in the hook", "no write in the hook");
                  ("pauses at putchar", "first putchar: paused");
                  ("restores the paused program", "restored: paused");
                  ( "replays the program",
                    "exited 0, exited 0, replays true, exit code 0" );
                  ("replaces the calls", "hllo\\\\ncrul\\\\nworld");
                ]);
          case
            ("script/unicorn/run/" ^ target ^ "-echo")
            (fun env ->
              let out =
                script env run ("bap:unicorn-executor" :: file :: api target)
              in
              sequence env out
                [
                  ("prints the arguments", "hello\ncruel\nworld");
                  ( "runs the components of the script",
                    "putchar was called true" );
                ]);
        ])
      echos

(* the semantics of the lifters, that lifters/check.ml compares with
   Unicorn, on the instructions of lifters/TARGET.insns, one of each
   mnemonic of the corpus of testsuite/src/corpus, whose results agree,
   in the parts of 32 instructions, which run in parallel, interpreted by
   Primus, in the cases lifters/TARGET/N, and run by the lifted engine,
   in the cases lifted/TARGET/N *)
let lifters data =
  let targets =
    [
      ("x86_64", "x86_64-linux-gnu-echo", []);
      ("i686", "i686-linux-gnu-threads-weird", []);
      ("aarch64", "aarch64-linux-gnu-echo", []);
      ("arm", "arm-linux-gnueabi-echo", []);
      ("thumb", "arm-linux-gnueabi-echo", [ "thumb" ]);
      ("mips", "mips-linux-gnu-echo", []);
      ("mips64", "mips64-linux-gnueabi-echo", []);
      ("mips32r6", "mipsisa32r6-linux-gnu-r6", [ "r6" ]);
      ("mips64r6", "mipsisa64r6-linux-gnuabi64-r6", [ "r6" ]);
      ("riscv64", "riscv64-linux-gnu-echo", []);
      ( "powerpc",
        "powerpc-linux-gnu-threads-weird",
        [ "api=" ^ path data "api/powerpc" ] );
    ]
  in
  let rec parts lines =
    match List.filteri (fun i _ -> i < 32) lines with
    | [] -> []
    | part -> part :: parts (List.filteri (fun i _ -> i >= 32) lines)
  in
  (* the lifted engine, see Bap_engine, runs the instructions, rather than
     Primus, in the cases lifted/TARGET/N *)
  List.concat_map
    (fun (kind, engine) ->
      List.concat_map
        (fun (target, bin, args) ->
          let insns = input ("lifters/" ^ target ^ ".insns") in
          In_channel.with_open_text insns In_channel.input_lines
          |> List.filter (fun l ->
              match String.index_opt l '#' with
              | Some i -> String.trim (String.sub l 0 i) <> ""
              | None -> String.trim l <> "")
          |> parts
          |> List.mapi (fun n part ->
              case
                (Printf.sprintf "%s/%s/%d" kind target (n + 1))
                (fun env ->
                  let insns =
                    write env "insns" (String.concat "\n" part ^ "\n")
                  in
                  let out =
                    bap ~timeout:300. env
                      ([
                         "script";
                         input "lifters/check.ml";
                         path data ("bin/" ^ bin);
                         insns;
                         "runs=2";
                       ]
                      @ args @ engine)
                  in
                  lacks env "the results differ" out "DIFF ";
                  has env "agrees with Unicorn" out
                    (Printf.sprintf "checked %d instructions, 0 differ"
                       (List.length part)))))
        targets)
    [ ("lifters", []); ("lifted", [ "engine=lifted" ]) ]

(* the traces of the lifted engine, see engines.ml, are the ones of
   Unicorn, but on x86, whose Unicorn reads the descriptors of the
   segments too *)
let engines data =
  List.map
    (fun target ->
      case ("lifted/traces/" ^ target) (fun env ->
          let out =
            bap ~timeout:300. env
              [
                "script";
                input "emu/engines.ml";
                path data ("bin/" ^ target ^ "-echo");
              ]
          in
          List.iter
            (fun blocks ->
              has env "records the same instructions and accesses" out
                ("blocks " ^ blocks
               ^ ": the instructions are the same true, the accesses true"))
            [ "false"; "true" ]))
    [
      "x86_64-linux-gnu";
      "aarch64-linux-gnu";
      "arm-linux-gnueabi";
      "mips-linux-gnu";
      "mips64-linux-gnueabi";
      "riscv64-linux-gnu";
    ]

(* the loaders: the sections of PE without the contents, e.g., .bss, are
   zero-filled segments, and the data objects, that the programs import,
   e.g., stdin, through the slots of the GOT, which the GLOB_DAT
   relocations, or the global entries of the GOT of MIPS, fill, have
   their storage, as the programs read them through the slots *)
let loaders data =
  List.map
    (fun (file, bss, size) ->
      case ("loader/pe-bss/" ^ file) (fun env ->
          let out = bap env [ "specification"; path data ("bin/" ^ file) ] in
          contains env "the .bss is a segment" out
            (Printf.sprintf "(segment %d %d true true false)" bss size);
          lacks env "the .bss is not in the file" out
            (Printf.sprintf "\\(mapped %d " bss)))
    [
      ("x86_64-w64-mingw32-symexec-guess", 0x407000, 0x990);
      ("i686-w64-mingw32-symexec-guess", 0x405000, 0x3f0);
    ]
  @ List.map
      (fun (file, image, iat) ->
        case ("loader/pe-imports/" ^ file) (fun env ->
            let out = bap env [ "specification"; path data ("bin/" ^ file) ] in
            contains env "maps the headers at the image base" out
              (Printf.sprintf "(segment %d " image);
            contains env "references the slots of the imports" out
              (Printf.sprintf "(external-reference %d DeleteCriticalSection)"
                 iat)))
      [
        ("x86_64-w64-mingw32-symexec-guess", 0x400000, 0x4081f4);
        ("i686-w64-mingw32-symexec-guess", 0x400000, 0x406104);
      ]
  @ List.concat_map
      (fun target ->
        List.concat_map
          (fun system ->
            [
              case
                ("loader/pe/" ^ system ^ "/" ^ target ^ "-symexec-guess")
                (fun env ->
                  let stdin = input "stdin/A" in
                  let out =
                    bap env ~timeout:120.
                      [
                        path data ("bin/" ^ target ^ "-symexec-guess");
                        "--passes=run";
                        "--run-systems=" ^ system;
                        "--primus-lisp-channel-redirect=<stdin>:" ^ stdin;
                      ]
                  in
                  contains env "runs the program of PE" out "access granted");
              case
                ("loader/pe/" ^ system ^ "/" ^ target ^ "-echo")
                (fun env ->
                  let out =
                    bap env ~timeout:120.
                      [
                        path data ("bin/" ^ target ^ "-echo");
                        "--passes=run";
                        "--run-systems=" ^ system;
                        "--run-argv=echo,hello,cruel,world";
                      ]
                  in
                  sequence env out
                    [
                      ("gets the arguments", "echo\nhello\ncruel\nworld");
                      ("ends", "course");
                    ]);
            ])
          [ "bap:stubbed-executor"; "bap:unicorn-executor" ])
      [ "x86_64-w64-mingw32"; "i686-w64-mingw32" ]
  @ List.concat_map
      (fun target ->
        List.map
          (fun system ->
            let name = target ^ "-symexec-crc32" in
            case
              ("loader/imports/" ^ system ^ "/" ^ name)
              (fun env ->
                let stdin = input "stdin/abc-abc" in
                let out =
                  bap env ~timeout:120.
                    ((path data ("bin/" ^ name) :: api data name)
                    @ [
                        "--passes=run";
                        "--run-systems=" ^ system;
                        "--primus-lisp-channel-redirect=<stdin>:" ^ stdin;
                      ])
                in
                contains env "reads stdin through the GOT" out "access granted"))
          [ "bap:stubbed-executor"; "bap:unicorn-executor" ])
      [
        "x86_64-linux-gnu";
        "aarch64-linux-gnu";
        "arm-linux-gnueabi";
        "mips-linux-gnu";
        "powerpc-linux-gnu";
      ]

(* the programs of src/loader of the testsuite, which clang and lld build
   without a libc, so that their layouts are unusual: the bss after the
   data in the middle of a page, the code and the data in the same page,
   the code, that is writable, the image at the top of the address space,
   the entry at the end of the code, the thread-local storage, the weak
   symbols, that nothing defines, the streams, that the programs import
   through the GOT, also without the sections, the tables of a PIE and an
   indirect function, and the programs of PE, whose bss is in the data,
   whose sections share the pages, whose image is at the top, and that
   import a function by its ordinal *)
let loader_layouts data =
  let expected name file =
    let wide =
      List.exists
        (fun p -> String.starts_with ~prefix:p file)
        [ "x86_64-"; "aarch64-"; "riscv64-" ]
    in
    match name with
    | "bss" -> Some "bss is zero 0\nbss end 5a\ndata 64\n"
    | "packed" -> Some "counter 2a\nconstant 63\n"
    | "rwx" -> Some "before a\nafter c\n"
    | "high" ->
        Some
          (Printf.sprintf "high 1234\naddress %s\n"
             (if wide then "7ffffff" else "fff"))
    | "entry" -> Some "entry 2a\n"
    | "tls" -> Some "initialized 77\nzeroed 0\nwritten 81\n"
    | "weak" -> Some "function 0\ndata 0\n"
    | "stdin" | "stdin-stripped" -> Some "read 41\n"
    | "pie" -> Some "table 6\nthird\nifunc 10\n"
    | "pe-basic" | "pe-merged" | "pe-packed" | "pe-high" ->
        Some "bss is zero 0\ndata 55\nfmode 8000\n"
    | _ -> None
  in
  files data "bin" (fun name -> contains_any [ "-loader-" ] name)
  (* the PLT entries of ARM, that lld makes, are named after the next
     slot, when the file has no sections, so the program calls putchar
     instead of fgetc, which is not fixed yet *)
  |> List.filter (fun file ->
      not
        (String.ends_with ~suffix:"arm-linux-gnueabi-loader-stdin-stripped" file))
  |> List.concat_map (fun file ->
      let base = Filename.basename file in
      (* the name of the case is after -loader- *)
      let rec after i =
        if String.sub base i 8 = "-loader-" then
          String.sub base (i + 8) (String.length base - i - 8)
        else after (i + 1)
      in
      let name = after 0 in
      List.map
        (fun system ->
          case
            ("loader/layout/" ^ system ^ "/" ^ base)
            (fun env ->
              let stdin = input "stdin/A" in
              let out =
                bap env ~timeout:60.
                  [
                    path data file;
                    "--passes=run";
                    "--run-systems=" ^ system;
                    "--primus-lisp-channel-redirect=<stdin>:" ^ stdin;
                  ]
              in
              match expected name base with
              | Some text -> contains env "prints the expected" out text
              | None ->
                  (* the function, that is imported by its ordinal, has
                     no name, so nothing links it, and the program stops
                     at its call *)
                  contains env "runs until the import" out "before 1\n";
                  lacks env "doesn't call the import" out "unnamed";
                  check env "ends" (out.status <> Timeout)))
        [
          "bap:stubbed-executor"; "bap:unicorn-executor"; "bap:lifted-executor";
        ])

let tests =
  [
    cff;
    sse;
    x86_floats;
    run;
    unicorn;
    syscall;
    timeout;
    checkpoint;
    unresolved;
    limit;
    debugging;
    lisp_cache;
    debugger;
    scripts;
    bare;
    emu;
    emu_signals;
    threads;
    emu_targets;
    lifters;
    engines;
    loaders;
    loader_layouts;
    observations;
    unicorn_taint;
    patched_code;
    unicorn_symexec;
    script_debugger;
    mprotect;
    smc;
    calloc;
    taint_bss;
    memory_hooks;
    taint_ops;
    taint_natives;
    printf_family;
    mmap;
    pages;
    taint;
    symexec;
  ]
