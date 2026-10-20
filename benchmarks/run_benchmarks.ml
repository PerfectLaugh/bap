(* runs the benchmarks, whose names contain one of the arguments, by
   default all of them, e.g., dune exec -- ./benchmarks/run_benchmarks.exe dom *)

let () =
  match Bap_main.init ~argv:[| "bap" |] () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@."
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () ->
      let only = List.tl (Array.to_list Sys.argv) in
      Eio_main.run @@ fun env ->
      Bench.run
        ~clock:(Eio.Stdenv.mono_clock env)
        ~only
        (List.concat [ Bench_dom.tests (); Bench_image.tests ])
