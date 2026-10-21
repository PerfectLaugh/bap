let () =
  let file = List.hd (Bap_script.args ()) in
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor" (Bap_script.project file))
