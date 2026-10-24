(* The options and the systems of the executors of the engines, which
   the plugins declare, primus-unicorn, whose options are
   --primus-unicorn-*, and whose systems are bap:unicorn-executor, ...,
   and primus-lifted, of the lifted engine, see Bap_lifted, whose options
   are --primus-lifted-*, and whose systems are bap:lifted-executor, ...
   The options are of the plugin, that declares them, when it loads. *)

open Core
open Bap_main
open Bap_primus.Std
module Executor = Primus_native_executor
module Native = Primus_native_libc

let package = "bap"

(* the loader is registered by the plugin, that initializes first *)
let loader_registered = ref false

(* [declare ~engine ~name] declares the options of the plugin, e.g.,
   [--primus-NAME-timeout], and the systems of the [engine], whose names
   are [bap:NAME-executor], ..., at the top level of the plugin *)
let declare ~(engine : Executor.kind) ~name ~doc ~runs_in =
  let option x = sprintf "--primus-%s-%s" name x in
  let timeout =
    Extension.Configuration.parameter
      Extension.Type.(some float)
      "timeout"
      ~doc:
        (sprintf
           "Terminates a Primus machine, after it has run for the given number \
            of seconds, both in %s and in Primus, e.g., in the Lisp stubs, by \
            the monotonic clock, not counting the pauses of the scripts."
           runs_in)
  in
  let checkpoint =
    Extension.Configuration.parameter
      Extension.Type.(some string)
      "checkpoint"
      ~doc:
        (sprintf
           "Saves the state of the Primus machine to the given file, when the \
            code at $(b,%s) runs in %s for the first time. The machine \
            continues to run after that."
           (option "checkpoint-at") runs_in)
  in
  let checkpoint_at =
    Extension.Configuration.parameter
      Extension.Type.(some string)
      "checkpoint-at"
      ~doc:
        (sprintf
           "The address, or the name of the subroutine, at which the \
            checkpoint of $(b,%s) is saved."
           (option "checkpoint"))
  in
  let restore =
    Extension.Configuration.parameter
      Extension.Type.(some string)
      "restore"
      ~doc:
        (sprintf
           "Continues from the checkpoint in the given file, which was saved \
            with $(b,%s), or by a script, see Bap_emu.save, for the same \
            program, instead of the first subroutine that the machine runs, \
            e.g., the entry point, with the names of the code and the \
            functions without their stubs, that the script saved too, and the \
            states of the components, e.g., the channels of Primus Lisp, whose \
            files are reopened, only if they are redirected now, or only read. \
            The checkpoint must be of the same file. The machine stops when \
            the subroutine, in which the checkpoint was saved, returns, after \
            the stub that called it completes, if it is known, e.g., \
            __libc_start_main exits with the result of main, as the code of \
            the stubs is not saved."
           (option "checkpoint"))
  in
  let native_stubs =
    Extension.Configuration.parameter
      Extension.Type.(list string =? Native.names)
      "native-stubs"
      ~doc:
        (sprintf
           "The functions of libc that run on the state of %s, instead of \
            their Lisp stubs, which copy the state to Primus and back. A \
            function runs natively, when the program calls it as an external \
            function, which Lisp implements, unless Lisp advises it, or the \
            code at its address is stopped at, e.g., by a debugger. The native \
            functions follow the C standard, and post the call and return \
            observations, but not those of Lisp. The empty list disables them. \
            The functions are %s."
           runs_in
           (String.concat ~sep:", " Native.names))
  in
  let jit =
    match engine with
    | `Unicorn -> None
    | `Lifted ->
        Some
          (Extension.Configuration.parameter
             Extension.Type.(bool =? true)
             "jit"
             ~doc:
               "Compiles the blocks of the lifted engine, that run often, with \
                the JIT of LLVM, to the native code of the host, rather than \
                runs only their closures.")
  in
  Extension.declare ~doc ~provides:[ "primus"; name ] @@ fun ctxt ->
  let options = Executor.options engine in
  options.timeout <- Extension.Configuration.get ctxt timeout;
  options.restore <- Extension.Configuration.get ctxt restore;
  Option.iter jit ~f:(fun jit ->
      options.jit <- Extension.Configuration.get ctxt jit);
  options.cache <-
    Option.map (Extension.Configuration.cachedir ()) ~f:(fun dir ->
        Stdlib.Filename.concat dir "lifted");
  options.digest <-
    String.concat ~sep:"\000"
      [
        Extension.Configuration.version;
        Extension.Configuration.build_id;
        Extension.Configuration.digest ctxt;
      ];
  let natives =
    List.filter
      (Extension.Configuration.get ctxt native_stubs)
      ~f:(Fn.non String.is_empty)
  in
  match
    List.find natives ~f:(fun name -> Option.is_none (Native.find name))
  with
  | Some stub ->
      Error
        (Extension.Error.Invalid
           (sprintf "%s: %s is not one of %s" (option "native-stubs") stub
              (String.concat ~sep:", " Native.names)))
  | None -> (
      options.native_stubs <- String.Set.of_list natives;
      (* the loader of both executors, see [Executor.engine_kind] *)
      if not !loader_registered then begin
        loader_registered := true;
        Primus.Components.register_generic ~package "load-binary-unicorn"
          (module Executor.Loader)
          ~desc:
            "Links the binary program, like load-binary, so that its \
             subroutines run in Unicorn, or in the lifted engine, see \
             bap:lifted-emulator, except those that other components replace, \
             e.g., with Lisp stubs."
      end;
      let engine_components =
        match engine with
        | `Unicorn -> []
        | `Lifted ->
            Primus.Components.register_generic ~package "lifted-emulator"
              (module Executor.Lifted_emulator)
              ~desc:
                "Runs the native code of the system, that load-binary-unicorn \
                 links, in the lifted engine, which runs the semantics of the \
                 instructions, that BAP lifts, see Bap_lifted, rather than in \
                 Unicorn.";
            [ "lifted-emulator" ]
      in
      let component = Primus.System.component ~package in
      let binary = sprintf "%s-binary-executor" name
      and executor = sprintf "%s-executor" name in
      (* bap:binary-executor with the loader instead of load-binary *)
      Primus.System.Repository.add
      @@ Primus.System.define ~package binary
           ~desc:(sprintf "Executes a binary program in %s." runs_in)
           ~components:
             (List.map ~f:component
                ([ "load-binary-unicorn" ] @ engine_components
                @ [
                    "program-loader";
                    "x86-registers-initializer";
                    "x86-setup-plt";
                    "powerpc-init";
                    "observation-printer";
                  ]));
      Primus.System.Repository.add
      @@ Primus.System.define ~package executor
           ~desc:
             (sprintf
                "Executes a binary in %s together with the Lisp Machine, which \
                 runs the stubs."
                runs_in)
           ~depends_on:
             [
               Primus.System.depends_on ~package binary;
               Primus.System.depends_on ~package "base-lisp-machine";
             ];
      (* bap:terminating-stubbed-executor in the engine *)
      Primus.System.Repository.add
      @@ Primus.System.define ~package
           (sprintf "terminating-%s-executor" name)
           ~desc:
             (sprintf
                "Executes a binary in %s together with the Lisp Machine, and \
                 limits the machines with bap:limit, see \
                 --primus-limit-max-length and --primus-limit-max-visited, \
                 which count only the code that Primus runs, e.g., the Lisp \
                 stubs, not the code in %s."
                runs_in runs_in)
           ~depends_on:[ Primus.System.depends_on ~package executor ]
           ~components:[ component "limit" ];
      match
        ( Extension.Configuration.get ctxt checkpoint,
          Extension.Configuration.get ctxt checkpoint_at )
      with
      | Some file, Some point ->
          options.checkpoint <- Some (file, point);
          Ok ()
      | None, None -> Ok ()
      | Some _, None ->
          Error
            (Extension.Error.Invalid
               (sprintf "%s requires %s" (option "checkpoint")
                  (option "checkpoint-at")))
      | None, Some _ ->
          Error
            (Extension.Error.Invalid
               (sprintf "%s requires %s" (option "checkpoint-at")
                  (option "checkpoint"))))
