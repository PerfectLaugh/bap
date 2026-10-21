(* the arguments are the program, and the directory of its syscalls.lisp *)
let () =
  match Bap_script.args () with
  | [ file; dir ] ->
      let lisp =
        Some { Bap_script.paths = [ dir ]; features = [ "syscalls" ] }
      in
      for _ = 1 to 2 do
        ignore
          (Bap_script.run ~system:"bap:unicorn-executor"
             (Bap_script.project ~bare:true ?lisp file))
      done
  | _ -> failwith "expected FILE LISP"
