let () =
  let file = List.hd (Bap_script.args ()) in
  ignore
    (Bap_script.run (Bap_script.project file))
