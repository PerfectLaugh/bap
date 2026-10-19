(* the tests of bap that run the binaries in the emulator *)

open Suite

(* runs the floating-point test of src/floats.c, which performs addition,
   division and comparison and prints PASS seven times *)
let floats name args data =
  [
    case name (fun env ->
        let out =
          bap env ((path data "sse/floats" :: args) @ [ "--passes=run" ])
        in
        let passes = count out "PASS" in
        check env
          (Printf.sprintf "expected 7 passes, got %d" passes)
          (passes = 7));
  ]

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
                  @ [
                      "--primus-lisp-type-check"; "--passes=run"; "--no-objdump";
                    ]
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
            path data ("bin/" ^ bin);
            "--passes=run";
            "--no-objdump";
            "--run-systems=" ^ system;
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
  @ List.map
      (fun system ->
        let bin = "arm-linux-gnueabihf-thumb-crc" in
        crc data (Printf.sprintf "run/%s/%s" system bin) bin system "1489580789")
      [ "bap:stubbed-executor"; "bap:legacy-main"; "bap:unicorn-executor" ]

(* the write system calls of Linux, which Primus Lisp doesn't model, so
   the cases define the intrinsics of the system calls *)
let syscalls =
  [
    ( "x86_64-linux-gnu-syscall-crc",
      {|(require stdio)
(defun syscall ()
  (declare (external "intrinsic:syscall"))
  (set RAX (if (= RAX 1) (write RDI RSI RDX) -1)))
|}
    );
    ( "aarch64-linux-gnu-svc-crc",
      {|(require stdio)
(defun svc ()
  (declare (external "intrinsic:svc"))
  (set R0 (if (= R8 64) (write R0 R1 R2) -1)))
|}
    );
  ]

let syscall data =
  List.concat_map
    (fun (bin, lisp) ->
      List.map
        (fun system ->
          case (Printf.sprintf "run/syscall/%s/%s" system bin) (fun env ->
              ignore (write env "syscalls.lisp" lisp);
              let out =
                bap env
                  [
                    path data ("bin/" ^ bin);
                    "--passes=run";
                    "--no-objdump";
                    "--run-systems=" ^ system;
                    "--primus-lisp-add=" ^ dir env;
                    "--primus-lisp-load=syscalls";
                  ]
              in
              contains env "prints the CRC" out "1489580789"))
        [ "bap:stubbed-executor"; "bap:unicorn-executor" ])
    syscalls

(* a program that never ends is terminated after the time in Unicorn *)
let timeout data =
  [
    case "run/unicorn/timeout" (fun env ->
        let out =
          bap ~timeout:120. env
            [
              path data "bin/x86_64-linux-gnu-forever";
              "--passes=run";
              "--no-objdump";
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
                "--no-objdump";
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
      ( "mips-linux-gnu-echo",
        [ ("jumps to the zero slot", "Segmentation fault at 0\\b") ] );
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
                "--no-objdump";
                "--run-systems=bap:terminating-unicorn-executor";
                Printf.sprintf "--primus-limit-max-length=%d" n;
              ]
          in
          check env "terminates" (out.status = Exited 0);
          if prints then contains env "prints everything" out "course"
          else lacks env "stops before it prints" out "hello"))
    [ (100, false); (1_000_000, true) ]

(* the primitives of Primus Lisp for debugging, in the advice of strcpy,
   which echo calls for its argument *)
let debugging data =
  let run env system lisp args =
    let _ = write env "debug.lisp" lisp in
    bap ~timeout:120. env
      ([
         path data "bin/x86_64-linux-gnu-echo";
         "--run-argv=hello";
         "--passes=run";
         "--no-objdump";
         "--run-systems=" ^ system;
         "--primus-lisp-add=" ^ dir env;
         "--primus-lisp-load=posix,debug";
         "--primus-lisp-type-check";
       ]
      @ args)
  in
  let advice body =
    Printf.sprintf
      "(defun debug (dst src)\n  (declare (advice :before strcpy))\n  %s)\n"
      body
  in
  List.concat_map
    (fun system ->
      [
        case ("lisp/dump-memory-region/" ^ system) (fun env ->
            let out =
              run env system
                (advice
                   "(memory-allocate 0x50000000 32 0x41)\n\
                   \  (memory-protect 0x50000010 16 0)\n\
                   \  (dump-memory-region 0x50000000 34)")
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
              run env system (advice "(bap-exit 7)")
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

(* the debugger stops the machines at the breakpoints and runs the
   commands of a file, the same in the interpreter and in Unicorn *)
let debugger data =
  let run env system bin commands args =
    let commands = write env "commands" commands in
    bap ~timeout:120. env
      ([
         path data ("bin/" ^ bin);
         "--passes=run";
         "--no-objdump";
         "--run-systems=" ^ system;
         "--run-components=bap:debugger";
         "--primus-debugger-commands=" ^ commands;
       ]
      @ args)
  in
  case "debugger/bap:unicorn-executor/x86_64-linux-gnu-crc-loop" (fun env ->
      let out =
        run env "bap:unicorn-executor" "x86_64-linux-gnu-crc-loop"
          "reg RAX\nset RAX 0\nstep\nstep\nc\n"
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
             let _ =
               write env "helpers.lisp"
                 "(defun arg-length ()\n  (strlen RDI))\n"
             in
             let out =
               run env system "x86_64-linux-gnu-echo"
                 "call arg-length\nstep\nd print_endline\nc\n"
                 [
                   "--run-argv=hello";
                   "--primus-debugger-break=print_endline";
                   "--primus-lisp-add=" ^ dir env;
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
  let script env source =
    bap ~timeout:300. env [ "script"; write env "script.ml" source; crc ]
  in
  [
    case "script/run" (fun env ->
        let out =
          script env
            {|let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ~options:[ "--run-systems=bap:unicorn-executor" ] ();
  ignore (Bap_script.run_pass "run" (Bap_script.project file))
|}
        in
        check env "exits" (out.status = Exited 0);
        contains env "runs the program" out "1635920155");
    case "script/primus" (fun env ->
        let out =
          script env
            {|#require "bap-primus"

open Bap.Std
open Bap_primus.Std

module Watch (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Env = Primus.Env.Make (Machine)

  let stopped addr =
    if Primus.Interpreter.Stops.mem addr then
      Env.get (Var.create "RAX" (Type.imm 64)) >>| fun x ->
      Printf.printf "RAX = %s\n%!"
        (Word.string_of_value (Primus.Value.to_word x))
    else Machine.return ()

  let init () = Primus.Interpreter.pc_change >>> stopped
end

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init
    ~options:
      [ "--run-systems=bap:unicorn-executor"; "--run-components=script:watch" ]
    ();
  Primus.Components.register_generic ~package:"script" "watch" (module Watch);
  Primus.Interpreter.Stops.add (Addr.of_int64 ~width:64 0x4004c0L);
  ignore (Bap_script.run_pass "run" (Bap_script.project file))
|}
        in
        lacks env "loads the plugins" out "Failed to load";
        sequence env out
          [ ("stops", "RAX = 9e7dd6e4"); ("runs the program", "1635920155") ]);
    case "script/error" (fun env ->
        let out = script env "let () =\n  print_endline 42\n" in
        check env "fails" (out.status = Exited 1);
        has env "tells the line of the script" out "script\\.ml\", line 2");
  ]

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
         "--no-objdump";
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
                "--no-objdump";
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

(* the program maps an anonymous page with mmap, runs the code that it
   writes there, after it makes it executable, and reads from the page,
   after it unmaps it, the interpreter can't run the code that it writes *)
let mmap data =
  [
    case "run/mmap/bap:unicorn-executor" (fun env ->
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-mmap";
              "--passes=run";
              "--no-objdump";
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
                "--no-objdump";
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

(* the legacy main system that explores all paths, as the promiscuous
   executor does *)
let promiscuous_main =
  {|(defsystem test:promiscuous-legacy-main
  :description "The legacy main system in the promiscuous mode."
  :depends-on (bap:legacy-main)
  :components (bap:var-randomizer
               bap:mem-randomizer
               bap:arg-randomizer
               bap:promiscuous-path-explorer
               bap:division-by-zero-handler
               bap:limit))
|}

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
              let systems = write env "promiscuous-main.asd" promiscuous_main in
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
  |> List.filter (fun file -> not (contains_any [ "mingw"; "mips" ] file))
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
                  "--run-in-isolation";
                ])
          in
          match out.status with
          | Stopped -> check env (file ^ " was hacked!") true
          | Timeout -> check env (file ^ " run out of time.") false
          | _ -> check env (file ^ " withhold the attack.") false))

let tests =
  [
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
    debugger;
    scripts;
    mprotect;
    mmap;
    pages;
    taint;
    symexec;
  ]
