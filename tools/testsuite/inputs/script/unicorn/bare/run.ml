(* the arguments are the program, and the directory of its syscalls.lisp,
   if the program needs it *)
let () =
  let file, lisp =
    match Bap_script.args () with
    | [ file ] -> (file, None)
    | [ file; dir ] ->
        (file, Some { Bap_script.paths = [ dir ]; features = [ "syscalls" ] })
    | _ -> failwith "expected FILE [LISP]"
  in
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor"
       ~args:[ "hello"; "cruel"; "world" ]
       (Bap_script.project ~bare:true ?lisp file))
