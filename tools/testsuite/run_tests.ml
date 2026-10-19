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
  [ sse; x86_floats; run; unicorn; syscall; timeout; mprotect; taint; symexec ]
