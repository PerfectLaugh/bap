open Core

let executable name =
  if String.contains name '/' then name
  else
    Stdlib.Sys.getenv_opt "PATH"
    |> Option.value ~default:"" |> String.split ~on:':'
    |> List.find_map ~f:(fun directory ->
        let path = Stdlib.Filename.concat directory name in
        try
          Caml_unix.access path [ Caml_unix.X_OK ];
          Some path
        with Caml_unix.Unix_error _ -> None)
    |> Option.value ~default:name

let run_process state ?script arguments =
  let arguments = Tui_model.command_args state ?script arguments in
  let program = executable Stdlib.Sys.argv.(0) in
  let stdout_path = Stdlib.Filename.temp_file "bap-tui-" ".stdout" in
  let stderr_path = Stdlib.Filename.temp_file "bap-tui-" ".stderr" in
  try
    let spawn () =
      let stdout =
        Caml_unix.openfile stdout_path
          [ Caml_unix.O_WRONLY; Caml_unix.O_TRUNC ]
          0o600
      in
      let stderr =
        Caml_unix.openfile stderr_path
          [ Caml_unix.O_WRONLY; Caml_unix.O_TRUNC ]
          0o600
      in
      Exn.protect
        ~f:(fun () ->
          Caml_unix.create_process program
            (Array.of_list (program :: arguments))
            Caml_unix.stdin stdout stderr)
        ~finally:(fun () ->
          Caml_unix.close stdout;
          Caml_unix.close stderr)
    in
    let _, status = Caml_unix.waitpid [] (spawn ()) in
    let output = In_channel.read_all stdout_path in
    let errors = In_channel.read_all stderr_path in
    let status_text =
      match status with
      | Caml_unix.WEXITED code -> sprintf "exit %d" code
      | Caml_unix.WSIGNALED signal -> sprintf "signal %d" signal
      | Caml_unix.WSTOPPED signal -> sprintf "stopped %d" signal
    in
    Stdlib.Sys.remove stdout_path;
    Stdlib.Sys.remove stderr_path;
    output ^ errors ^ "\n" ^ status_text
  with exn ->
    (try Stdlib.Sys.remove stdout_path with _ -> ());
    (try Stdlib.Sys.remove stderr_path with _ -> ());
    Exn.to_string exn

let scroll (state : Tui_model.state) amount =
  { state with Tui_model.scroll = Int.max 0 (state.scroll + amount) }

let utf8 char =
  let buffer = Stdlib.Buffer.create 4 in
  Stdlib.Buffer.add_utf_8_uchar buffer char;
  Stdlib.Buffer.contents buffer

let prompt term label state =
  let rec loop buffer =
    Tui_view.matrix
      { state with Tui_model.status = label ^ buffer }
      (LTerm.size term)
    |> LTerm.render term |> Lwt_main.run;
    match Lwt_main.run (LTerm.read_event term) with
    | LTerm_event.Key { code = LTerm_key.Enter; _ } -> Some buffer
    | LTerm_event.Key { code = LTerm_key.Escape; _ } -> None
    | LTerm_event.Key { code = LTerm_key.Backspace; _ } ->
        loop
          (if String.is_empty buffer then buffer
           else String.prefix buffer (String.length buffer - 1))
    | LTerm_event.Key { code = LTerm_key.Char char; _ } ->
        loop (buffer ^ utf8 char)
    | LTerm_event.Resize _ -> loop buffer
    | _ -> loop buffer
  in
  loop ""

let words text =
  String.split ~on:' ' text
  |> List.filter ~f:(fun word -> not (String.is_empty word))

let handle term state key =
  let continue state = `Continue state in
  match LTerm_key.to_string_compact key with
  | "q" -> `Stop
  | "j" | "Down" -> continue (Tui_model.move state 1)
  | "k" | "Up" -> continue (Tui_model.move state (-1))
  | "h" | "Left" -> continue (Tui_model.cycle_view state (-1))
  | "l" | "Right" | "Tab" -> continue (Tui_model.cycle_view state 1)
  | "Next_page" -> continue (scroll state 10)
  | "Prev_page" -> continue (scroll state (-10))
  | "Home" -> continue (Tui_model.select state 0)
  | "End" ->
      continue
        (Tui_model.select state (List.length (Tui_model.filtered state) - 1))
  | "Enter" -> continue (Tui_model.set_view state Tui_model.Decompile)
  | "[" -> continue (Tui_model.next_memory_region state (-1))
  | "]" -> continue (Tui_model.next_memory_region state 1)
  | "/" ->
      Option.value_map (prompt term "/" state) ~default:(continue state)
        ~f:(fun text -> continue (Tui_model.set_filter state text))
  | "n" -> continue (Tui_model.move state 1)
  | "N" -> continue (Tui_model.move state (-1))
  | "a" ->
      Option.value_map (prompt term "address: " state) ~default:(continue state)
        ~f:(fun text -> continue (Tui_model.select_address state text))
  | "c" ->
      continue
        {
          state with
          Tui_model.concise = not state.concise;
          status = (if state.concise then "default" else "concise");
        }
  | "r" -> (
      match Tui_model.load ~concise:state.concise state.file with
      | Error error ->
          continue { state with Tui_model.status = Error.to_string_hum error }
      | Ok fresh ->
          continue
            { fresh with Tui_model.view = state.view; filter = state.filter })
  | "o" ->
      Option.value_map (prompt term "open: " state) ~default:(continue state)
        ~f:(fun file ->
          match Tui_model.load ~concise:state.concise file with
          | Error error ->
              continue
                { state with Tui_model.status = Error.to_string_hum error }
          | Ok fresh -> continue fresh)
  | "p" ->
      let state = Tui_model.set_view state Tui_model.Passes in
      Option.value_map (prompt term "pass: " state) ~default:(continue state)
        ~f:(fun name ->
          match Tui_model.run_pass state name with
          | Error error ->
              continue
                { state with Tui_model.status = Error.to_string_hum error }
          | Ok state -> continue state)
  | "w" ->
      let state = Tui_model.set_view state Tui_model.Writers in
      Option.value_map (prompt term "writer: " state) ~default:(continue state)
        ~f:(fun name ->
          continue
            {
              state with
              Tui_model.view = Tui_model.Console;
              console_output = Tui_model.writer_text state.project name;
            })
  | "e" ->
      Option.value_map (prompt term "export: " state) ~default:(continue state)
        ~f:(fun path ->
          try
            Out_channel.write_all path ~data:(Tui_model.text state);
            continue
              { state with Tui_model.status = sprintf "Exported %s" path }
          with exn ->
            continue { state with Tui_model.status = Exn.to_string exn })
  | ":" ->
      Option.value_map (prompt term "bap " state) ~default:(continue state)
        ~f:(fun command ->
          continue
            {
              state with
              Tui_model.view = Tui_model.Console;
              console_output = run_process state (words command);
            })
  | "s" ->
      Option.value_map (prompt term "script: " state) ~default:(continue state)
        ~f:(fun script ->
          continue
            {
              state with
              Tui_model.view = Tui_model.Console;
              console_output = run_process state ~script [];
            })
  | "?" -> continue (Tui_model.set_view state Tui_model.Help)
  | _ -> continue state

let run state =
  let rec loop term state =
    Tui_view.matrix state (LTerm.size term) |> LTerm.render term |> Lwt_main.run;
    match Lwt_main.run (LTerm.read_event term) with
    | LTerm_event.Resize _ -> loop term state
    | LTerm_event.Key key -> (
        match handle term state key with
        | `Stop -> Ok ()
        | `Continue state -> loop term state)
    | _ -> loop term state
  in
  let cleanup term mode =
    Lwt_main.run
      (Lwt.bind (LTerm.leave_raw_mode term mode) (fun () ->
           Lwt.bind (LTerm.show_cursor term) (fun () ->
               Lwt.bind (LTerm.clear_screen term) (fun () -> LTerm.flush term))))
  in
  let term =
    Lwt_main.run
      (LTerm.create Lwt_unix.stdin Lwt_io.stdin Lwt_unix.stdout Lwt_io.stdout)
  in
  let mode = Lwt_main.run (LTerm.enter_raw_mode term) in
  Stdlib.Fun.protect
    ~finally:(fun () -> cleanup term mode)
    (fun () ->
      Lwt_main.run (LTerm.hide_cursor term);
      loop term state)
