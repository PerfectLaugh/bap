#require "bap-primus"

open Bap_primus.Std

let calls = ref 0

module Count (Machine : Primus.Machine.S) = struct
  let call (name, _) =
    if String.equal name "putchar" then incr calls;
    Machine.return ()

  let init () = Machine.Observation.observe Primus.Linker.Trace.call call
end

let () =
  match Bap_script.args () with
  | system :: file :: api ->
      ignore
        (Bap_script.run ~system
           ~init:[ (module Count) ]
           ~args:[ "hello"; "cruel"; "world" ]
           (Bap_script.project ~disassemble:true ~api file));
      Printf.printf "\nputchar was called %b\n" (!calls > 20)
  | _ -> failwith "expected SYSTEM FILE [API]"
