open Core
open Bap.Std
open Bap_core_theory
open Bap_tui

let check name condition = if not condition then failwith name

let subroutine name =
  let exit = Jmp.create_ret (Direct (Tid.create ())) in
  Sub.create ~name ~blks:[ Blk.create ~jmps:[ exit ] () ] ()

let project () =
  let target = Theory.Target.get ~package:"bap" "x86_64" in
  let program =
    Program.create ~subs:[ subroutine "alpha"; subroutine "beta" ] ()
  in
  Project.with_program (Project.empty target) program

let test_navigation () =
  let state = Tui_model.create (project ()) "sample" in
  check "initial selection"
    (Option.value_map (Tui_model.selected state) ~default:false ~f:(fun func ->
         String.equal func.Tui_model.name "alpha"));
  let state = Tui_model.move state 1 in
  check "move selection"
    (Option.value_map (Tui_model.selected state) ~default:false ~f:(fun func ->
         String.equal func.Tui_model.name "beta"));
  check "selection clamped" ((Tui_model.move state 1).selected = 1);
  let filtered = Tui_model.set_filter state "ALPHA" in
  check "case insensitive filter" (List.length (Tui_model.filtered filtered) = 1);
  check "filter resets selection" (filtered.selected = 0);
  check "view wrap"
    (Poly.equal (Tui_model.cycle_view filtered (-1)).view
       (List.last_exn Tui_model.views));
  check "concise name escaping"
    (String.equal (Tui_model.decompiled_name "operator+") "fn_operator_")

let test_commands () =
  let state = Tui_model.create (project ()) "program image" in
  check "default command"
    (List.equal String.equal
       (Tui_model.command_args state [])
       [ "disassemble"; "program image" ]);
  check "script command"
    (List.equal String.equal
       (Tui_model.command_args state ~script:"analysis.ml" [])
       [ "script"; "analysis.ml"; "program image" ]);
  check "arbitrary command has no implicit file"
    (List.equal String.equal
       (Tui_model.command_args state [ "list"; "targets" ])
       [ "list"; "targets" ]);
  check "explicit current file"
    (List.equal String.equal
       (Tui_model.command_args state [ "disassemble"; "$file" ])
       [ "disassemble"; "program image" ])

let test_rendering () =
  let state = Tui_model.create (project ()) "sample" in
  List.iter [ 0; 1; 23; 24; 59; 60; 80; 120 ] ~f:(fun cols ->
      List.iter [ 0; 1; 7; 8; 24 ] ~f:(fun rows ->
          let rendered =
            Tui_view.matrix state { LTerm_geom.rows; cols }
            |> Tui_view.matrix_to_string
          in
          check "minimum rendering height"
            (List.length (String.split_lines rendered) >= 8)));
  let dump = Tui_view.dump state in
  check "dump title" (String.is_substring dump ~substring:"BAP Workspace");
  check "dump functions" (String.is_substring dump ~substring:"alpha");
  check "dump decompilation" (String.is_substring dump ~substring:"fn_alpha")

let test_real_project () =
  Bap_llvm.Std.init_loader ();
  match Stdlib.Sys.getenv_opt "TEST_TUI_BINARY" with
  | None -> ()
  | Some file -> (
      match Tui_model.load ~loader:"llvm" file with
      | Error error -> failwith (Error.to_string_hum error)
      | Ok state -> check "loaded file identity" (String.equal state.file file))

let test_cli () =
  match
    (Stdlib.Sys.getenv_opt "TEST_BAP", Stdlib.Sys.getenv_opt "TEST_TUI_BINARY")
  with
  | Some bap, Some file ->
      let input, output =
        Caml_unix.open_process_args bap
          [| bap; "tui"; "--dump"; "--concise"; file |]
      in
      let rendered = In_channel.input_all input in
      let status = Caml_unix.close_process (input, output) in
      check "cli exit status" (Poly.equal status (Caml_unix.WEXITED 0));
      check "cli workspace"
        (String.is_substring rendered ~substring:"BAP Workspace");
      check "cli concise mode"
        (String.is_substring rendered ~substring:"concise")
  | _ -> ()

let () =
  test_navigation ();
  test_commands ();
  test_rendering ();
  test_real_project ();
  test_cli ()
