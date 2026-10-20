open Core
open Bap_main
open Bap_primus.Std

let package = "bap"

let timeout =
  Extension.Configuration.parameter
    Extension.Type.(some float)
    "timeout"
    ~doc:
      "Terminates a Primus machine, after it has run for the given number of \
       seconds of the processor time, both in Unicorn and in Primus, e.g., in \
       the Lisp stubs."

let checkpoint =
  Extension.Configuration.parameter
    Extension.Type.(some string)
    "checkpoint"
    ~doc:
      "Saves the state of the Primus machine to the given file, when the code \
       at $(b,--primus-unicorn-checkpoint-at) runs in Unicorn for the first \
       time. The machine continues to run after that."

let checkpoint_at =
  Extension.Configuration.parameter
    Extension.Type.(some string)
    "checkpoint-at"
    ~doc:
      "The address, or the name of the subroutine, at which the checkpoint of \
       $(b,--primus-unicorn-checkpoint) is saved."

let restore =
  Extension.Configuration.parameter
    Extension.Type.(some string)
    "restore"
    ~doc:
      "Continues from the checkpoint in the given file, which was saved with \
       $(b,--primus-unicorn-checkpoint), or by a script, see Bap_emu.save, for \
       the same program, instead of the first subroutine that the machine \
       runs, e.g., the entry point, with the names of the code and the \
       functions without their stubs, that the script saved too, and the \
       states of the components, e.g., the channels of Primus Lisp. The \
       checkpoint must be of the same file. The machine stops when the \
       subroutine, in which the checkpoint was saved, returns, after the stub \
       that called it completes, if it is known, e.g., __libc_start_main exits \
       with the result of main, as the code of the stubs is not saved."

let native_stubs =
  let module Native = Bap_primus_unicorn_plugin.Primus_unicorn_native in
  Extension.Configuration.parameter
    Extension.Type.(list string =? Native.names)
    "native-stubs"
    ~doc:
      (sprintf
         "The functions of libc that run on the state of Unicorn, instead of \
          their Lisp stubs, which copy the state to Primus and back. A \
          function runs natively, when the program calls it as an external \
          function, which Lisp implements, unless Lisp advises it, or the code \
          at its address is stopped at, e.g., by a debugger. The native \
          functions follow the C standard, and post the call and return \
          observations, but not those of Lisp. The empty list disables them. \
          The functions are %s."
         (String.concat ~sep:", " Native.names))

let () =
  Extension.declare ~doc:"runs the binary programs in Primus with Unicorn"
    ~provides:[ "primus"; "unicorn" ]
  @@ fun ctxt ->
  let module Executor = Bap_primus_unicorn_plugin.Primus_unicorn_executor in
  Executor.timeout := Extension.Configuration.get ctxt timeout;
  Executor.restore := Extension.Configuration.get ctxt restore;
  let module Native = Bap_primus_unicorn_plugin.Primus_unicorn_native in
  let natives =
    List.filter
      (Extension.Configuration.get ctxt native_stubs)
      ~f:(Fn.non String.is_empty)
  in
  match
    List.find natives ~f:(fun name -> Option.is_none (Native.find name))
  with
  | Some name ->
      Error
        (Extension.Error.Invalid
           (sprintf "--primus-unicorn-native-stubs: %s is not one of %s" name
              (String.concat ~sep:", " Native.names)))
  | None -> (
      Executor.native_stubs := String.Set.of_list natives;
      Primus.Components.register_generic ~package "load-binary-unicorn"
        (module Bap_primus_unicorn_plugin.Primus_unicorn_executor.Loader)
        ~desc:
          "Links the binary program, like load-binary, so that its subroutines \
           run in the Unicorn CPU emulator, except those that other components \
           replace, e.g., with Lisp stubs.";
      let component = Primus.System.component ~package in
      (* bap:binary-executor with load-binary-unicorn instead of load-binary *)
      Primus.System.Repository.add
      @@ Primus.System.define ~package "unicorn-binary-executor"
           ~desc:"Executes a binary program in Unicorn."
           ~components:
             (List.map ~f:component
                [
                  "load-binary-unicorn";
                  "program-loader";
                  "x86-registers-initializer";
                  "x86-setup-plt";
                  "powerpc-init";
                  "observation-printer";
                ]);
      Primus.System.Repository.add
      @@ Primus.System.define ~package "unicorn-executor"
           ~desc:
             "Executes a binary in Unicorn together with the Lisp Machine, \
              which runs the stubs."
           ~depends_on:
             [
               Primus.System.depends_on ~package "unicorn-binary-executor";
               Primus.System.depends_on ~package "base-lisp-machine";
             ];
      (* bap:terminating-stubbed-executor with Unicorn *)
      Primus.System.Repository.add
      @@ Primus.System.define ~package "terminating-unicorn-executor"
           ~desc:
             "Executes a binary in Unicorn together with the Lisp Machine, and \
              limits the machines with bap:limit, see \
              --primus-limit-max-length and --primus-limit-max-visited, which \
              count only the code that Primus runs, e.g., the Lisp stubs, not \
              the code in Unicorn."
           ~depends_on:[ Primus.System.depends_on ~package "unicorn-executor" ]
           ~components:[ component "limit" ];
      match
        ( Extension.Configuration.get ctxt checkpoint,
          Extension.Configuration.get ctxt checkpoint_at )
      with
      | Some file, Some point ->
          Executor.checkpoint := Some (file, point);
          Ok ()
      | None, None -> Ok ()
      | Some _, None ->
          Error
            (Extension.Error.Invalid
               "--primus-unicorn-checkpoint requires \
                --primus-unicorn-checkpoint-at")
      | None, Some _ ->
          Error
            (Extension.Error.Invalid
               "--primus-unicorn-checkpoint-at requires \
                --primus-unicorn-checkpoint"))
