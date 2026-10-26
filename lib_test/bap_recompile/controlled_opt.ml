let () =
  let output = Sys.getenv "BAP_RECOMPILE_TEST_OUTPUT" in
  let rec destination = function
    | [] | [ _ ] -> failwith "controlled_opt: missing -o destination"
    | "-o" :: path :: _ -> path
    | _ :: rest -> destination rest
  in
  let channel = open_out_bin (destination (List.tl (Array.to_list Sys.argv))) in
  output_string channel output;
  close_out channel
