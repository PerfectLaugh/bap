open Core
open Bap.Std
open LTerm_geom

let text_style = LTerm_style.none

let title_style =
  {
    LTerm_style.none with
    LTerm_style.bold = Some true;
    foreground = Some LTerm_style.cyan;
  }

let selected_style = { LTerm_style.none with LTerm_style.reverse = Some true }

let tab_style =
  { LTerm_style.none with LTerm_style.foreground = Some LTerm_style.yellow }

let status_style =
  { LTerm_style.none with LTerm_style.foreground = Some LTerm_style.green }

let draw context row col ?(style = text_style) text =
  LTerm_draw.draw_string context row col ~style (Zed_string.of_utf8 text)

let matrix state size =
  let size = { rows = Int.max 8 size.rows; cols = Int.max 24 size.cols } in
  let matrix = LTerm_draw.make_matrix size in
  let context = LTerm_draw.context matrix size in
  let function_width =
    if size.cols < 60 then 0 else Int.min 34 (Int.max 22 (size.cols / 4))
  in
  let content_left = function_width in
  let content_width = size.cols - content_left in
  draw context 0 0 ~style:title_style
    (sprintf "BAP Workspace | %s | %s" state.Tui_model.file
       (Tui_model.view_name state.Tui_model.view));
  if function_width > 0 then
    LTerm_draw.draw_frame_labelled context
      { row1 = 2; col1 = 0; row2 = size.rows - 3; col2 = function_width - 1 }
      (Zed_string.of_utf8 "Functions")
      LTerm_draw.Light;
  LTerm_draw.draw_frame_labelled context
    {
      row1 = 2;
      col1 = content_left;
      row2 = size.rows - 3;
      col2 = size.cols - 1;
    }
    (Zed_string.of_utf8
       (match Tui_model.selected state with
       | Some func -> Tui_model.view_name state.view ^ " | " ^ func.name
       | None -> Tui_model.view_name state.view))
    LTerm_draw.Light;
  let functions = Tui_model.filtered state in
  let height = Int.max 1 (size.rows - 6) in
  let first =
    Int.max 0
      (Int.min (state.selected - (height / 2)) (List.length functions - height))
  in
  if function_width > 0 then
    List.iteri (List.drop functions first) ~f:(fun index func ->
        if index < height then
          let selected = index + first = state.selected in
          let name =
            match func.Tui_model.addr with
            | Some addr -> sprintf "%s %s" (Addr.string_of_value addr) func.name
            | None -> func.name
          in
          draw context (index + 4) 1
            ~style:(if selected then selected_style else text_style)
            (String.prefix name (function_width - 2)));
  let tabs =
    List.map Tui_model.views ~f:(fun view ->
        let name = Tui_model.view_name view in
        if Poly.equal view state.view then "[" ^ name ^ "]"
        else " " ^ name ^ " ")
    |> String.concat ~sep:""
  in
  draw context 3 (content_left + 1) ~style:tab_style
    (String.prefix tabs (content_width - 2));
  let text = Tui_model.text state in
  let lines = String.split_lines text in
  let visible = Int.max 1 (size.rows - 8) in
  let scroll =
    Int.max 0 (Int.min state.scroll (Int.max 0 (List.length lines - visible)))
  in
  List.iteri (List.drop lines scroll) ~f:(fun index line ->
      if index < visible then
        draw context (index + 5) (content_left + 1)
          (String.prefix line (content_width - 2)));
  draw context (size.rows - 2) 0 ~style:status_style
    (String.prefix
       (sprintf "%s | %d/%d | %s" state.status (state.selected + 1)
          (List.length functions)
          (if state.concise then "concise" else "default"))
       size.cols);
  draw context (size.rows - 1) 0
    "j/k: navigate  h/l: views  /: filter  c: concise  p: passes  w: writers  \
     :: command  q: quit";
  matrix

let matrix_to_string matrix =
  Array.to_list matrix
  |> List.map ~f:(fun row ->
      Array.to_list row
      |> List.map ~f:(fun point ->
          match !point with
          | LTerm_draw.Elem elem -> Zed_char.to_utf8 elem.LTerm_draw.char
          | LTerm_draw.WidthHolder _ -> " ")
      |> String.concat ~sep:"")
  |> String.concat ~sep:"\n"

let dump state = matrix state { rows = 24; cols = 80 } |> matrix_to_string
