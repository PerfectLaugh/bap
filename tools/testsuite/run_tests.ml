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
    (* the machines take Unicorn from each other, while their bytes are
       in Unicorn, see Primus.Memory.Backing, and print the same, except
       the argument, that one of them changes, while its pages are
       parked *)
    case "script/unicorn/fork" (fun env ->
        let out =
          bap ~timeout:300. env
            [
              "script";
              write env "script.ml"
                {|#require "bap-primus, monads"

open Core
open Bap.Std
open Bap_primus.Std

(* forks the machine at the third putchar, and then switches between
   the parent and the child at each putchar, so that they take Unicorn
   from each other in the middle of their runs, and the parent, which
   doesn't run in Unicorn, capitalizes its argument world *)
module Fork (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Env = Primus.Env.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)

  let calls = ref 0
  let machines = ref []
  let patched = ref false

  (* the string, to which a word of the stack points, e.g., the copy of
     the argument in the heap, which echo prints *)
  let find_string sp text =
    Memory.load_bytes sp 0x1000 >>= fun bytes ->
    let word i =
      List.init 8 ~f:(fun k ->
          match bytes.(i + k) with Some (c, _) -> Char.to_int c | None -> 0)
      |> List.foldi ~init:0L ~f:(fun k acc b ->
          Int64.(acc lor shift_left (of_int b) Int.(8 * k)))
    in
    let pointers =
      List.init (0x1000 / 8) ~f:(fun i -> Addr.of_int64 ~width:64 (word (i * 8)))
    in
    Machine.List.find pointers ~f:(fun p ->
        Memory.load_bytes p (String.length text) >>| fun bytes ->
        String.equal text
          (String.of_array
             (Array.map bytes ~f:(function Some (c, _) -> c | None -> '?'))))

  let capitalize () =
    Machine.current () >>= fun self ->
    match !machines with
    | parent :: _
      when Monads.Std.Monad.State.Multi.Id.equal parent self && not !patched ->
        patched := true;
        Env.get (Var.create "RSP" (Type.imm 64)) >>= fun sp ->
        find_string (Primus.Value.to_word sp) "world\000" >>= (function
        | Some p -> Memory.store p (Word.of_int ~width:8 (Char.to_int 'W'))
        | None -> Machine.return ())
    | _ -> Machine.return ()

  let switch () =
    Machine.forks () >>= fun alive ->
    Machine.current () >>= fun self ->
    let others =
      List.filter !machines ~f:(fun id ->
          (not (Monads.Std.Monad.State.Multi.Id.equal id self))
          && Seq.exists alive ~f:(Monads.Std.Monad.State.Multi.Id.equal id))
    in
    match others with
    | other :: _ -> Machine.switch other
    | [] -> Machine.return ()

  let call (name, _) =
    if String.equal name "putchar" then begin
      incr calls;
      if !calls = 3 then
        Machine.current () >>= fun parent ->
        Machine.fork () >>= fun () ->
        Machine.current () >>= fun self ->
        if Monads.Std.Monad.State.Multi.Id.equal self parent then Machine.return ()
        else begin
          machines := [ parent; self ];
          Machine.return ()
        end
      else if !calls > 3 then switch () >>= capitalize
      else Machine.return ()
    end
    else Machine.return ()

  let init () = Primus.Linker.Trace.call >>> call
end

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  Bap_script.init
    ~options:
      [
        "--run-systems=bap:unicorn-executor";
        "--run-components=script:fork";
        "--run-argv=hello,cruel,world";
      ]
    ();
  Primus.Components.register_generic ~package:"script" "fork" (module Fork);
  ignore (Bap_script.run_pass "run" (Bap_script.project file))
|};
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
    case "script/error" (fun env ->
        let out = script env "let () =\n  print_endline 42\n" in
        check env "fails" (out.status = Exited 1);
        has env "tells the line of the script" out "script\\.ml\", line 2");
  ]

(* the bare projects of the scripts, which are not disassembled, run in
   Unicorn as the disassembled ones: from their entry points, with the
   functions in the Thumb encoding from the symbol table, and the system
   calls lifted on demand *)
let bare data =
  let run env ?(options = []) bin =
    let options =
      List.map (Printf.sprintf "%S")
        ([
           "--run-systems=bap:unicorn-executor"; "--run-argv=hello,cruel,world";
         ]
        @ options)
    in
    bap ~timeout:300. env
      [
        "script";
        write env "script.ml"
          (Printf.sprintf
             {|let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ~options:[ %s ] ();
  ignore (Bap_script.run_pass "run" (Bap_script.project ~bare:true file))
|}
             (String.concat "; " options));
        path data ("bin/" ^ bin);
      ]
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
        ignore
          (write env "syscalls.lisp"
             (List.assoc "aarch64-linux-gnu-svc-crc" syscalls));
        let out =
          run env "aarch64-linux-gnu-svc-crc"
            ~options:
              [ "--primus-lisp-add=" ^ dir env; "--primus-lisp-load=syscalls" ]
        in
        contains env "prints the CRC" out "1489580789");
    case "script/unicorn/bare/mips-linux-gnu-echo" (fun env ->
        let out = run env "mips-linux-gnu-echo" in
        sequence env out
          [ ("prints the arguments", "hello"); ("ends", "course") ]);
    case "script/unicorn/bare/x86_64-linux-gnu-syscall-crc" (fun env ->
        ignore
          (write env "syscalls.lisp"
             (List.assoc "x86_64-linux-gnu-syscall-crc" syscalls));
        let out =
          run env "x86_64-linux-gnu-syscall-crc"
            ~options:
              [ "--primus-lisp-add=" ^ dir env; "--primus-lisp-load=syscalls" ]
        in
        contains env "prints the CRC" out "1489580789");
  ]

(* the scripts run the programs with Bap_emu, pause them, see and change
   their registers and memory, hook their instructions, stores and calls,
   and restore their snapshots *)
let emu data =
  let script env bin source =
    bap ~timeout:300. env
      [ "script"; write env "script.ml" source; path data ("bin/" ^ bin) ]
  in
  [
    case "emu/x86_64-linux-gnu-echo/main" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo"
            {|#require "bap-primus-unicorn.emu"
open Bap.Std
module Emu = Bap_emu

let word emu addr =
  let s = Emu.read emu addr 8 in
  let r = ref 0L in
  for i = 7 downto 0 do r := Int64.(logor (shift_left !r 8) (of_int (Char.code s.[i]))) done;
  !r

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ();
  let emu = Emu.create ~args:[ "hello"; "cruel"; "world" ] (Bap_script.project ~bare:true file) in
  Printf.printf "paused at the entry %Lx\n%!" (Emu.pc emu);
  (match Emu.run emu ~until:0x40076bL with
  | Paused -> Printf.printf "paused at main %Lx, argc = %Ld\n%!" (Emu.pc emu) (Emu.reg emu "RDI")
  | _ -> failwith "main is not reached");
  let argv = Emu.reg emu "RSI" in
  let arg1 = word emu Int64.(add argv 8L) in
  Printf.printf "argv[1] = %s\n%!" (Emu.read emu arg1 5);
  Emu.write emu arg1 "HELLO";
  let stores = ref 0 in
  Emu.on_write emu (fun _ _ _ _ -> incr stores);
  Emu.on_call emu "putchar" (fun emu ->
      if Emu.arg emu 0 = Int64.of_int (Char.code 'l') then Return 108L else Default);
  (match Emu.run emu with
  | Exited code ->
      Printf.printf "exited with %s after %d stores\n"
        (match code with Some c -> string_of_int c | None -> "?") !stores
  | Paused -> print_endline "paused"
  | Failed msg -> print_endline ("failed: " ^ msg))
|}
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
          script env "x86_64-linux-gnu-echo"
            {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu

let show emu = function
  | Emu.Paused -> Printf.printf "paused at %Lx\n%!" (Emu.pc emu)
  | Exited c -> Printf.printf "exited %s\n%!" (match c with Some c -> string_of_int c | None -> "?")
  | Failed m -> Printf.printf "failed %s\n%!" m

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ();
  let emu = Emu.create ~args:[ "hello"; "cruel" ] (Bap_script.project ~bare:true file) in
  (* three steps from the entry *)
  for _ = 1 to 3 do show emu (Emu.step emu) done;
  (* the first instruction of print_strings stops the program *)
  let stopped = ref false in
  Emu.on_code emu ~first:0x400733L ~last:0x400733L (fun emu _ ->
      if not !stopped then (stopped := true; Emu.stop emu));
  show emu (Emu.run emu);
  (* print_endline, a function of the program, prints nothing for the
     arguments, but the strings of the program *)
  let calls = ref 0 in
  Emu.on_call emu "print_endline" (fun _ ->
      incr calls; if !calls <= 3 then Return 0L else Default);
  show emu (Emu.run emu);
  Printf.printf "print_endline was called %d times\n" !calls
|}
        in
        sequence env out
          [
            ("steps", "paused at 400602\npaused at 400605\npaused at 400606");
            ("stops in a hook", "paused at 400733");
            ("replaces a function of the program", "\nwe\n");
            ("calls it", "print_endline was called 11 times");
          ]);
    (* the patched code stays, after the snapshot forks the machine, and
       after it is restored, which Bap_emu.write doesn't guarantee *)
    (* the script reads and writes the state of the machine in Primus *)
    case "emu/x86_64-linux-gnu-echo/primus" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo"
            {|#require "bap-primus-unicorn.emu"
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ();
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project ~bare:true file) in
  ignore (Emu.run emu ~until:0x40076bL);
  let argc = ref Word.b0 in
  let module Get (Machine : Primus.Machine.S) = struct
    module Env = Primus.Env.Make (Machine)
    module Value = Primus.Value.Make (Machine)
    open Machine.Syntax

    let init () =
      Env.get (Var.create "RDI" reg64_t) >>= fun x ->
      argc := Primus.Value.to_word x;
      Value.of_int ~width:64 7 >>= Env.set (Var.create "RDI" reg64_t)
  end in
  Emu.primus emu (module Get);
  Printf.printf "argc %s in Primus, %Ld in Unicorn\n%!" (Word.to_string !argc)
    (Emu.reg emu "RDI")
|}
        in
        contains env "reads and writes the registers" out
          "argc 2:64u in Primus, 7 in Unicorn");
    (* the script taints the input, which the code in Unicorn uses, and
       sees the jumps, that it taints, as the Lisp does, see taint/ *)
    case "emu/x86_64-linux-gnu-symexec-crc32/taint" (fun env ->
        let input = write env "input" "abc\nabd\n" in
        let out =
          script env "x86_64-linux-gnu-symexec-crc32"
            (Printf.sprintf
               {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ~options:[ "--primus-lisp-channel-redirect=<stdin>:%s" ] ();
  let emu = Emu.create ~components:Emu.Taint.components (Bap_script.project file) in
  (match Emu.run emu ~until:0x80cL with
   | Paused -> ()
   | _ -> failwith "fgets didn't return");
  let rbp = Emu.reg emu "RBP" in
  Emu.Taint.introduce emu ~kind:"input" (Mem (Int64.sub rbp 0x40L, 16));
  Emu.Taint.introduce emu ~kind:"input" (Mem (Int64.sub rbp 0x30L, 16));
  Printf.printf "buf1 %%s, RAX %%s\n%%!"
    (String.concat "," (Emu.Taint.kinds emu (Mem (Int64.sub rbp 0x40L, 4))))
    (String.concat "," (Emu.Taint.kinds emu (Reg "RAX")));
  let jumps = ref [] in
  Emu.Taint.on_jump emu (fun _ ~kinds dst -> jumps := (dst, kinds) :: !jumps);
  ignore (Emu.run emu);
  Printf.printf "jumps:";
  List.iter (fun (dst, kinds) ->
      Printf.printf " %%Lx:%%s" dst (String.concat "," kinds)) (List.rev !jumps);
  print_newline ()
|}
               input)
        in
        contains env "taints the buffer, not RAX" out "buf1 input, RAX \n";
        contains env "sees the tainted jumps" out
          "jumps: 752:input 752:input 752:input 752:input 7b8:input 752:input \
           752:input 752:input 752:input 7b8:input 83b:input");
    (* the scripts make the registers and the memory symbolic, and the
       solver finds the inputs, that flip the branches *)
    case "emu/x86_64-linux-gnu-symexec-guess/symbolic" (fun env ->
        let input = write env "input" "Z" in
        let out =
          script env "x86_64-linux-gnu-symexec-guess"
            (Printf.sprintf
               {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu
module Sym = Emu.Symbolic

let model = function
  | None -> "unsat"
  | Some m ->
      String.concat ","
        (List.map (fun (n, v) -> Printf.sprintf "%%s=%%Lx" n (Int64.logand v 0xffL)) m)

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ~options:[ "--primus-lisp-channel-redirect=<stdin>:%s" ] ();
  let emu = Emu.create ~components:Sym.components (Bap_script.project file) in
  (match Emu.run emu ~until:0x693L with
   | Paused -> ()
   | _ -> failwith "getchar didn't return");
  Sym.symbolize emu (Reg "RAX");
  Printf.printf "RAX %%s, RBX %%s\n%%!"
    (String.concat "," (List.map (Option.value ~default:"-") (Sym.formula emu (Reg "RAX"))))
    (String.concat "," (List.map (Option.value ~default:"-") (Sym.formula emu (Reg "RBX"))));
  let branches = ref [] in
  Sym.on_branch emu (fun _ b -> branches := b :: !branches);
  ignore (Emu.run emu);
  List.iter (fun b ->
      Printf.printf "branch %%Lx %%b flips with %%s\n" (Sym.addr b) (Sym.taken b)
        (model (Sym.flip b))) (List.rev !branches)
|}
               input)
        in
        contains env "makes RAX symbolic" out "RAX RAX, RBX -\n";
        contains env "flips the branch" out "branch 696 true flips with RAX=41");
    case "emu/x86_64-linux-gnu-symexec-crc32/symbolic" (fun env ->
        let input = write env "input" "abc\nabd\n" in
        let out =
          script env "x86_64-linux-gnu-symexec-crc32"
            (Printf.sprintf
               {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu
module Sym = Emu.Symbolic

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init
    ~options:[ "--primus-lisp-channel-redirect=<stdin>:%s";
               "--primus-symbolic-executor-timeout=10000" ] ();
  let emu = Emu.create ~components:Sym.components (Bap_script.project file) in
  (match Emu.run emu ~until:0x80cL with
   | Paused -> ()
   | _ -> failwith "fgets didn't return");
  let buf1 = Int64.sub (Emu.reg emu "RBP") 0x40L in
  Sym.symbolize emu (Mem (buf1, 4));
  let branches = ref [] in
  Sym.on_branch emu (fun _ b -> branches := b :: !branches);
  ignore (Emu.run emu);
  Printf.printf "branches:";
  List.iter (fun b -> Printf.printf " %%Lx" (Sym.addr b)) (List.rev !branches);
  print_newline ();
  match Sym.flip (List.hd !branches) with
  | None -> print_endline "no collision"
  | Some m ->
      print_string "collision: ";
      List.iter (fun (_, v) -> print_char (Char.chr (Int64.to_int v))) m;
      print_newline ()
|}
               input)
        in
        contains env "sees the symbolic branches" out
          "branches: 7b6 7b6 7b6 7b6 82d\n";
        contains env "finds the collision of the CRC" out "collision: abd\n");
    case "emu/x86_64-linux-gnu-echo/patch" (fun env ->
        let out =
          script env "x86_64-linux-gnu-echo"
            {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu

let status = function
  | Emu.Exited _ -> print_endline "exited"
  | Paused -> print_endline "paused"
  | Failed m -> print_endline ("failed: " ^ m)

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ();
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project ~bare:true file) in
  ignore (Emu.run emu ~until:0x40076bL);
  (* mov $0xa, %edi, which prints the newline, prints + instead *)
  Emu.patch emu 0x400727L "\xbf\x2b";
  let snapshot = Emu.snapshot emu in
  status (Emu.run emu);
  Emu.restore emu snapshot;
  status (Emu.run emu)
|}
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
          script env "x86_64-linux-gnu-echo"
            {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu

let word emu addr =
  let s = Emu.read emu addr 8 in
  let r = ref 0L in
  for i = 7 downto 0 do r := Int64.(logor (shift_left !r 8) (of_int (Char.code s.[i]))) done;
  !r

let show emu = function
  | Emu.Paused -> Printf.printf "paused at %Lx\n%!" (Emu.pc emu)
  | Exited c -> Printf.printf "exited %s\n%!" (match c with Some c -> string_of_int c | None -> "?")
  | Failed m -> Printf.printf "failed %s\n%!" m

let () =
  let file = List.hd (Bap_script.args ()) in
  Bap_script.init ();
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project ~bare:true file) in
  show emu (Emu.run emu ~until:0x40076bL);
  let snap = Emu.snapshot emu in
  let arg1 () = word emu Int64.(add (Emu.reg emu "RSI") 8L) in
  Printf.printf "snapshot at %Lx, RDI = %Ld, argv[1] = %s\n%!" (Emu.pc emu) (Emu.reg emu "RDI") (Emu.read emu (arg1 ()) 5);
  print_endline "== first run";
  show emu (Emu.run emu);
  Emu.restore emu snap;
  Printf.printf "restored at %Lx, RDI = %Ld, argv[1] = %s\n%!" (Emu.pc emu) (Emu.reg emu "RDI") (Emu.read emu (arg1 ()) 5);
  Emu.write emu (arg1 ()) "WORLD";
  Emu.set_reg emu "RDI" 2L;
  print_endline "== second run, argv[1] = WORLD, argc = 2";
  show emu (Emu.run emu);
  Emu.restore emu snap;
  Printf.printf "restored again, RDI = %Ld, argv[1] = %s\n%!" (Emu.reg emu "RDI") (Emu.read emu (arg1 ()) 5);
  print_endline "== third run";
  show emu (Emu.run emu ~until:0x400733L);
  show emu (Emu.run emu)
|}
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
    case "emu/arm-linux-gnueabihf-thumb-crc" (fun env ->
        let out =
          script env "arm-linux-gnueabihf-thumb-crc"
            {|#require "bap-primus-unicorn.emu"
module Emu = Bap_emu
let () =
  let file = List.hd (Bap_script.args ()) in
  let bare = Sys.getenv_opt "BARE" <> Some "0" in
  Bap_script.init ();
  let emu = Emu.create ~args:[ "hi" ] (Bap_script.project ~bare file) in
  let pcs = List.init 3 (fun _ -> ignore (Emu.step emu); Printf.sprintf "%Lx" (Emu.pc emu)) in
  Printf.printf "steps: %s\n%!" (String.concat " " pcs);
  match Emu.run emu with
  | Exited c -> Printf.printf "exited %s\n" (match c with Some c -> string_of_int c | None -> "?")
  | Paused -> print_endline "paused"
  | Failed m -> print_endline ("failed: " ^ m)
|}
        in
        sequence env out
          [
            ("steps the Thumb code", "steps: 202df 202e1 202e3");
            ("prints the CRC", "1489580789");
            ("exits", "exited 0");
          ]);
  ]

(* the observers of Lisp see the instructions, the loads and the stores
   of the code, which runs in Unicorn, as they see those of the
   interpreter, except the loads, which the semantics of x86 repeat *)
let observations data =
  let run env system =
    ignore
      (write env "counts.lisp"
         {|(defparameter *pcs* 0)
(defparameter *stores* 0)
(defparameter *loads* 0)
(defmethod pc-changed (pc) (incr *pcs*))
(defmethod stored (a x) (incr *stores*))
(defmethod loaded (a x) (incr *loads*))
(defmethod fini () (msg "pcs $0 stores $1 loads $2" *pcs* *stores* *loads*))
|});
    bap env
      [
        path data "bin/x86_64-linux-gnu-echo";
        "--passes=run";
        "--no-objdump";
        "--run-argv=echo,hello";
        "--run-systems=" ^ system;
        "--primus-lisp-add=" ^ dir env;
        "--primus-lisp-load=posix,counts";
        "--primus-print-observations=lisp-message";
      ]
  in
  [
    case "run/unicorn/observations" (fun env ->
        let out = run env "bap:unicorn-executor" in
        contains env "sees the events" out "pcs 0x508 stores 0x883 loads 0xE1D");
    case "run/stubbed-executor/observations" (fun env ->
        let out = run env "bap:stubbed-executor" in
        contains env "sees the events" out "pcs 0x507 stores 0x86B loads 0x11E9");
  ]

(* the taint of the input, which Lisp introduces, propagates through
   the code, that uses it, which Primus interprets, while the rest runs
   in Unicorn, so the observers see the same tainted jumps, i.e., of
   the loop of the CRC, which ends after the 4 bytes of each line, and
   of the comparison of the CRCs *)
let unicorn_taint data =
  let run env system =
    let input = write env "input" "abc\nabd\n" in
    ignore
      (write env "tainting.lisp"
         {|(defparameter *tainted* 0)

(defmethod call-return (name buf n _ ret)
  (when (= name 'fgets)
    (taint-introduce-indirectly 'input buf n)))

(defmethod jumping (c dst)
  (when (taint-get-direct 'input c)
    (msg "tainted jump to $0" dst)
    (incr *tainted*)))

(defmethod fini () (msg "tainted $0 jumps" *tainted*))
|});
    bap env
      [
        path data "bin/x86_64-linux-gnu-symexec-crc32";
        "--passes=run";
        "--no-objdump";
        "--run-systems=" ^ system;
        "--primus-lisp-channel-redirect=<stdin>:" ^ input;
        "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
        "--primus-lisp-add=" ^ dir env;
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
    [ "bap:stubbed-executor"; "bap:unicorn-executor" ]

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
        let input = write env "input" "abc\nabd\n" in
        ignore
          (write env "patching.lisp"
             {|(defparameter *patched* nil)

(defmethod call-return (name buf n _ ret)
  (when (= name 'fgets)
    (taint-introduce-indirectly 'input buf n)))

(defmethod jumping (c dst)
  (when (taint-get-direct 'input c)
    (msg "tainted jump to $0" dst)
    (unless *patched*
      (set *patched* true)
      (memory-protect 0x7B6 1 7)
      (memory-write 0x7B6 0x74:8)
      (memory-protect 0x7B6 1 5))))
|});
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-symexec-crc32";
              "--passes=run";
              "--no-objdump";
              "--run-systems=" ^ system;
              "--primus-lisp-channel-redirect=<stdin>:" ^ input;
              "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
              "--primus-lisp-add=" ^ dir env;
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
  let echo (arch, addr, bytes, sep) system =
    case
      ("run/patched-code/" ^ system ^ "/" ^ arch ^ "-echo")
      (fun env ->
        let patch =
          List.fold_left
            (fun dst byte ->
              Printf.sprintf "(memory-write %s 0x%02x:8)" dst byte)
            addr bytes
        in
        ignore
          (write env "patching.lisp"
             (Printf.sprintf
                {|(defparameter *patched* nil)

(defmethod call-return (name s n)
  (when (and (= name 'strlen) (not *patched*))
    (set *patched* true)
    (memory-protect %s 4 7)
    %s
    (memory-protect %s 4 5)))
|}
                addr patch addr));
        let out =
          bap env
            ([ path data ("bin/" ^ arch ^ "-echo") ]
            @ api data arch
            @ [
                "--passes=run";
                "--no-objdump";
                "--run-argv=echo,hello,world";
                "--run-systems=" ^ system;
                "--primus-lisp-add=" ^ dir env;
                "--primus-lisp-load=posix,patching";
              ])
        in
        contains env "prints the patched separator" out
          (String.concat sep [ "echo"; "hello"; "world"; "we" ]))
  in
  let echos =
    [
      ("x86_64-linux-gnu", "0x400728", [ 0x2b ], "+");
      ("x86-linux-gnu", "0x804856f", [ 0x2b ], "+");
      ("aarch64-linux-gnu", "0xaa0", [ 0x60; 0x05; 0x80; 0x52 ], "+");
      ("arm-linux-gnueabi", "0x85b4", [ 0x2b ], "+");
      ("mips-linux-gnu", "0x4008fb", [ 0x2b ], "+");
      ("mips64-linux-gnueabi", "0x120000d8b", [ 0x2b ], "+");
      ("powerpc32-linux-gnu", "0x10000673", [ 0x2b ], "+");
      ("riscv64-linux-gnu", "0x10734", [ 0x25; 0x45 ], "\t");
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
        ignore
          (write env "patching.lisp"
             (Printf.sprintf
                {|(defparameter *patched* nil)

(defmethod call (name c)
  (when (and (= name 'putchar) (not *patched*))
    (set *patched* true)
    %s
    (memory-protect 0x202d0 2 7)
    (memory-write 0x202d0 0x2b:8)
    (memory-protect 0x202d0 2 5)))

%s
|}
                (if taint then
                   "(taint-introduce-indirectly 'stack (- SP 64) 128)"
                 else "")
                (if taint then
                   {|(defmethod jumping (c dst) (msg "interpreted jump to $0" dst))|}
                 else "")));
        let out =
          bap env
            ([
               path data "bin/arm-linux-gnueabihf-thumb-crc";
               "--passes=run";
               "--no-objdump";
               "--run-systems=" ^ system;
               "--primus-lisp-add=" ^ dir env;
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
    case name (fun env ->
        ignore
          (write env "generating.lisp"
             (Printf.sprintf
                {|(defparameter *patched* nil)

(defmethod call (name c)
  (when (and (= name 'putchar) (not *patched*))
    (set *patched* true)
    %s
    (memory-allocate 0x8000 0x1000)
    (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write (memory-write
        0x8000 0x00:8) 0xb5:8) 0x00:8) 0xf0:8) 0x7e:8) 0xe8:8) 0x18:8) 0xf0:8)
        0x8c:8) 0xe9:8) 0x00:8) 0xbd:8)
    (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write (memory-write (memory-write
        0x8100 0x2b:8) 0x00:8) 0xa0:8) 0xe3:8) 0x1e:8) 0xff:8) 0x2f:8) 0xe1:8)
    (memory-protect 0x8000 0x1000 5)
    (memory-protect 0x202d0 6 7)
    (memory-write (memory-write (memory-write (memory-write (memory-write
      (memory-write 0x202d0 0x48:8) 0xf2:8) 0x01:8) 0x03:8) 0x98:8) 0x47:8)
    (memory-protect 0x202d0 6 5)))

%s
|}
                (if taint then "(taint-introduce-indirectly 'code 0x8000 0x200)"
                 else "")
                (if taint then
                   {|(defmethod jumping (c dst) (msg "interpreted jump to $0" dst))|}
                 else "")));
        let out =
          bap env
            ([
               path data "bin/arm-linux-gnueabihf-thumb-crc";
               "--passes=run";
               "--no-objdump";
               "--run-systems=" ^ system;
               "--primus-lisp-add=" ^ dir env;
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
        if taint then
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
  List.map taint systems @ List.map thumb systems
  @ List.map (generated ~taint:false) systems
  @ [ generated ~taint:true "bap:unicorn-executor" ]
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
              [
                path data ("bin/" ^ name);
                "--passes=run";
                "--run-systems=bap:unicorn-executor";
                "--run-components=bap:greedy-scheduler,bap:symbolic-computer,bap:symbolic-path-explorer,bap:symbolic-path-constraints,bap:symbolic-lisp-primitives";
                "--primus-lisp-load=symbolic-stdio,posix";
                "--primus-symbolic-executor-cutoff-level=16";
                "--primus-symbolic-executor-timeout=1000";
                "--run-in-isolation";
              ]
          in
          match out.status with
          | Stopped -> check env (name ^ " was hacked!") true
          | Exited _ when matches out "access" ->
              check env (name ^ " was hacked!") true
          | _ -> check env (name ^ " withhold the attack.") false))
    [
      "x86_64-linux-gnu-symexec-simple";
      "x86_64-linux-gnu-symexec-input";
      "x86_64-linux-gnu-symexec-guess";
    ]

(* the scripts stop the machines with Bap_script_debugger, and see and
   change them in their handlers, the same in the interpreter and in
   Unicorn *)
let script_debugger data =
  let script env source args =
    bap ~timeout:300. env ("script" :: write env "script.ml" source :: args)
  in
  case "script/debugger/bap:unicorn-executor/x86_64-linux-gnu-crc-loop"
    (fun env ->
      let out =
        script env
          {|#require "bap-primus, bap-frontend.script-debugger"

open Bap.Std
open Bap_primus.Std
module Debugger = Bap_script_debugger

(* zeroes the CRC, at the breakpoint, and shows the next instruction *)
module Zero (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Eval = Primus.Interpreter.Make (Machine)

  let rax = Var.create "RAX" (Type.imm 64)
  let steps = ref 0

  let stopped addr =
    if !steps = 0 then begin
      incr steps;
      Debugger.step true;
      Eval.get rax >>= fun x ->
      Printf.printf "at %s RAX = %s, zeroing it\n%!" (Addr.string_of_value addr)
        (Word.string_of_value (Primus.Value.to_word x));
      Eval.const (Word.zero 64) >>= Eval.set rax
    end
    else begin
      Debugger.step false;
      Primus.Interpreter.Stops.remove (Addr.of_int64 ~width:64 0x4004c0L);
      Printf.printf "stepped to %s\n%!" (Addr.string_of_value addr);
      Machine.return ()
    end
end

let () =
  Debugger.break "0x4004c0";
  Debugger.on_stop (module Zero);
  Bap_script.init ~options:[ "--run-systems=bap:unicorn-executor" ] ();
  ignore
    (Bap_script.run_pass "run"
       (Bap_script.project (List.hd (Bap_script.args ()))))
|}
          [ path data "bin/x86_64-linux-gnu-crc-loop" ]
      in
      sequence env out
        [
          ("stops", "at 4004c0 RAX = 9e7dd6e4");
          ("steps", "stepped to 4004c2");
          ("prints the CRC of zero", "4294967295");
        ])
  :: List.map
       (fun system ->
         case
           ("script/debugger/" ^ system ^ "/x86_64-linux-gnu-echo")
           (fun env ->
             let out =
               script env
                 {|#require "bap-primus, bap-frontend.script-debugger"

open Bap_primus.Std
module Debugger = Bap_script_debugger

let calls = ref 0

module Count (Machine : Primus.Machine.S) = struct
  let stopped _ =
    incr calls;
    Machine.return ()
end

let () =
  let system, file =
    match Bap_script.args () with
    | [ system; file ] -> (system, file)
    | _ -> failwith "expected SYSTEM FILE"
  in
  Debugger.break "print_endline";
  Debugger.on_stop (module Count);
  Bap_script.init ~options:[ "--run-systems=" ^ system; "--run-argv=hello" ] ();
  ignore (Bap_script.run_pass "run" (Bap_script.project file));
  Printf.printf "print_endline was called %d times\n" !calls
|}
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
   after it unmaps it *)
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
    (* the interpreter runs the code, that the program writes, as it is
       in the memory, see Primus.Lift *)
    case "run/mmap/bap:stubbed-executor" (fun env ->
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-mmap";
              "--passes=run";
              "--no-objdump";
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
        ignore
          (write env "stack.lisp"
             {|(defmethod call-return (name p n prot ret)
  (when (= name 'mprotect)
    (taint-introduce-indirectly 'stack (- RSP 64) 128)))
|});
        let out =
          bap env
            [
              path data "bin/x86_64-linux-gnu-mmap";
              "--passes=run";
              "--no-objdump";
              "--run-systems=bap:unicorn-executor";
              "--run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy";
              "--primus-lisp-add=" ^ dir env;
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
    bare;
    emu;
    observations;
    unicorn_taint;
    patched_code;
    unicorn_symexec;
    script_debugger;
    mprotect;
    mmap;
    pages;
    taint;
    symexec;
  ]
