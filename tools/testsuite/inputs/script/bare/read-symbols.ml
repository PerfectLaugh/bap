open Bap.Std

let () =
  let file = List.hd (Bap_script.args ()) in
  let prog = Project.program (Bap_script.project file) in
  Term.enum sub_t prog
  |> Seq.iter ~f:(fun sub ->
      match Term.get_attr sub address with
      | Some addr -> Format.printf "%s %a@." (Sub.name sub) Addr.pp addr
      | None -> ())
