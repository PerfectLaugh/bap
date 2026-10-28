open Core
open Bap.Std
open Bap_core_theory
open Regular.Std

type view =
  | Decompile
  | Disassembly
  | Bir
  | Cfg
  | Symbols
  | Memory
  | Info
  | Passes
  | Writers
  | Console
  | Help

type func = { tid : Tid.t; name : string; addr : Word.t option }

type state = {
  project : Project.t;
  file : string;
  concise : bool;
  view : view;
  functions : func list;
  selected : int;
  filter : string;
  scroll : int;
  memory_offset : int;
  console_output : string;
  status : string;
  recovered : (bool, Bap_decompile.Ast.program) Hashtbl.Poly.t;
}

let clamp value lo hi = Int.max lo (Int.min hi value)

let views =
  [
    Decompile;
    Disassembly;
    Bir;
    Cfg;
    Symbols;
    Memory;
    Info;
    Passes;
    Writers;
    Console;
    Help;
  ]

let view_name = function
  | Decompile -> "Decompile"
  | Disassembly -> "Disassembly"
  | Bir -> "BIR"
  | Cfg -> "CFG"
  | Symbols -> "Symbols/Xrefs"
  | Memory -> "Memory"
  | Info -> "Info"
  | Passes -> "Passes"
  | Writers -> "Writers"
  | Console -> "BAP console"
  | Help -> "Help"

let functions project =
  Term.enum sub_t (Project.program project)
  |> Seq.map ~f:(fun sub ->
      {
        tid = Term.tid sub;
        name = Sub.name sub;
        addr = Term.get_attr sub address;
      })
  |> Seq.to_list
  |> List.sort ~compare:(fun left right ->
      match (left.addr, right.addr) with
      | Some left, Some right -> Word.compare left right
      | _ -> String.compare left.name right.name)

let create ?(concise = false) project file =
  {
    project;
    file;
    concise;
    view = Decompile;
    functions = functions project;
    selected = 0;
    filter = "";
    scroll = 0;
    memory_offset = 0;
    console_output = "";
    status = "Ready";
    recovered = Hashtbl.Poly.create ();
  }

let load ?(concise = false) ?loader ?target file =
  Project.Input.load ?loader ?target file
  |> Project.create ~package:file
  |> Result.map ~f:(fun project -> create ~concise project file)

let filtered state =
  List.filter state.functions ~f:(fun func ->
      String.is_substring
        (String.lowercase func.name)
        ~substring:(String.lowercase state.filter))

let selected state =
  let functions = filtered state in
  if List.is_empty functions then None
  else List.nth functions (clamp state.selected 0 (List.length functions - 1))

let select state index =
  let count = List.length (filtered state) in
  let selected = if count = 0 then 0 else clamp index 0 (count - 1) in
  { state with selected; scroll = 0 }

let move state delta = select state (state.selected + delta)
let set_view state view = { state with view; scroll = 0 }

let cycle_view state direction =
  let rec find index = function
    | [] -> 0
    | view :: rest ->
        if Poly.equal view state.view then index else find (index + 1) rest
  in
  let current = find 0 views in
  let next = (current + direction + List.length views) mod List.length views in
  set_view state (List.nth_exn views next)

let set_filter state filter = { (select state 0) with filter }

let select_address state text =
  match Int64.of_string text with
  | exception _ -> { state with status = sprintf "Invalid address %S" text }
  | value -> (
      let matches =
        List.filteri state.functions ~f:(fun _ func ->
            match func.addr with
            | Some addr -> Int64.equal (Word.to_int64_exn addr) value
            | None -> false)
      in
      match matches with
      | [] -> { state with status = sprintf "No function at 0x%Lx" value }
      | func :: _ ->
          let filtered = filtered state in
          let index =
            List.findi filtered ~f:(fun _ other -> Tid.equal other.tid func.tid)
            |> Option.map ~f:fst |> Option.value ~default:0
          in
          { (select state index) with status = sprintf "Selected %s" func.name }
      )

let writer_text project name =
  match Project.find_writer name with
  | None -> sprintf "Writer %s is not available" name
  | Some writer -> Data.Write.to_bigstring writer project |> Bigstring.to_string

let sub state =
  Option.map (selected state) ~f:(fun func ->
      Term.find_exn sub_t (Project.program state.project) func.tid)

let decompiled_name name =
  "fn_"
  ^ String.map name ~f:(fun char ->
      if Char.is_alphanum char || Char.equal char '_' then char else '_')

let decompile state =
  let recovered =
    Hashtbl.find_or_add state.recovered state.concise ~default:(fun () ->
        Bap_decompile.decompile ~concise:state.concise
          ~target:(Project.target state.project)
          ~memory:(Project.memory state.project)
          (Project.program state.project))
  in
  match selected state with
  | None -> Bap_decompile.to_string recovered
  | Some func ->
      let expected = decompiled_name func.name in
      let functions =
        List.filter recovered.Bap_decompile.Ast.functions ~f:(fun func ->
            String.equal func.Bap_decompile.Ast.name expected)
      in
      Bap_decompile.to_string { recovered with Bap_decompile.Ast.functions }

let bir state =
  match sub state with
  | Some sub -> Sub.to_string sub
  | None -> "No function selected"

let info state =
  let target = Project.target state.project in
  String.concat ~sep:"\n"
    [
      sprintf "File: %s" state.file;
      sprintf "Target: %s" (KB.Name.show (Theory.Target.name target));
      sprintf "Architecture: %s" (Arch.to_string (Project.arch state.project));
      sprintf "Bits: %d" (Theory.Target.bits target);
      sprintf "Functions: %d" (List.length state.functions);
      sprintf "Concise: %b" state.concise;
      sprintf "Libraries: %d" (List.length (Project.libraries state.project));
      sprintf "Memory regions: %d"
        (Memmap.length (Project.memory state.project));
      state.status;
    ]

let symbol_xrefs state =
  let program = Project.program state.project in
  let callers, callees =
    match selected state with
    | None -> ([], [])
    | Some selected ->
        Term.enum sub_t program
        |> Seq.fold ~init:([], []) ~f:(fun (callers, callees) sub ->
            Term.enum blk_t sub
            |> Seq.fold ~init:(callers, callees)
                 ~f:(fun (callers, callees) blk ->
                   Term.enum jmp_t blk
                   |> Seq.fold ~init:(callers, callees)
                        ~f:(fun (callers, callees) jmp ->
                          match Jmp.kind jmp with
                          | Call call -> (
                              match Call.target call with
                              | Direct tid when Tid.equal tid selected.tid ->
                                  (Sub.name sub :: callers, callees)
                              | Direct tid when Tid.equal tid (Term.tid sub) ->
                                  ( callers,
                                    Sub.name (Term.find_exn sub_t program tid)
                                    :: callees )
                              | _ -> (callers, callees))
                          | _ -> (callers, callees))))
  in
  String.concat ~sep:"\n"
    [
      sprintf "Function: %s"
        (Option.value_map (selected state) ~default:"<none>" ~f:(fun func ->
             func.name));
      "";
      "Callers:";
      String.concat ~sep:"\n"
        (List.dedup_and_sort ~compare:String.compare callers);
      "";
      "Callees:";
      String.concat ~sep:"\n"
        (List.dedup_and_sort ~compare:String.compare callees);
    ]

let passes state =
  Project.passes ()
  |> List.map ~f:Project.Pass.name
  |> List.sort ~compare:String.compare
  |> String.concat ~sep:"\n"

let writers _state =
  Data.all_writers ()
  |> List.concat_map ~f:(fun (typename, writers) ->
      List.map writers ~f:(fun (name, `Ver version, description) ->
          sprintf "%s (%s) %s: %s" typename version name
            (Option.value description ~default:"")))
  |> List.sort ~compare:String.compare
  |> String.concat ~sep:"\n"

let hex_byte mem addr =
  match Memory.get ~scale:`r8 ~addr mem with
  | Ok value -> Word.to_int_exn value
  | Error _ -> 0

let memory_line mem addr length =
  let bytes =
    List.init length ~f:(fun index -> hex_byte mem (Addr.nsucc addr index))
  in
  let hex = String.concat ~sep:" " (List.map bytes ~f:(sprintf "%02x")) in
  let ascii =
    String.map
      (String.of_char_list (List.map bytes ~f:Char.of_int_exn))
      ~f:(fun char -> if Char.is_print char then char else '.')
  in
  sprintf "%s  %-47s  %s" (Addr.string_of_value addr) hex ascii

let memory state =
  let regions =
    Memmap.to_sequence (Project.memory state.project) |> Seq.to_list
  in
  match List.nth regions state.memory_offset with
  | None -> "No memory regions"
  | Some (mem, _) ->
      let length = Memory.length mem in
      let lines =
        Seq.range 0 (Int.min 64 ((length + 15) / 16))
        |> Seq.map ~f:(fun index ->
            let offset = index * 16 in
            memory_line mem
              (Addr.nsucc (Memory.min_addr mem) offset)
              (Int.min 16 (length - offset)))
        |> Seq.to_list
      in
      String.concat ~sep:"\n"
        (sprintf "Region %d/%d: %s..%s" (state.memory_offset + 1)
           (List.length regions)
           (Addr.string_of_value (Memory.min_addr mem))
           (Addr.string_of_value (Memory.max_addr mem))
        :: lines)

let next_memory_region state delta =
  let count = Memmap.length (Project.memory state.project) in
  {
    state with
    memory_offset =
      clamp (state.memory_offset + delta) 0 (Int.max 0 (count - 1));
  }

let selected_project state =
  match sub state with
  | None -> state.project
  | Some sub ->
      Project.with_program state.project (Program.create ~subs:[ sub ] ())

let text state =
  match state.view with
  | Decompile -> decompile state
  | Disassembly -> writer_text (selected_project state) "asm"
  | Bir -> bir state
  | Cfg -> writer_text (selected_project state) "cfg"
  | Symbols -> symbol_xrefs state
  | Memory -> memory state
  | Info -> info state
  | Passes -> passes state
  | Writers -> writers state
  | Console ->
      if String.is_empty state.console_output then
        "Use : for a BAP command or s for a script"
      else state.console_output
  | Help ->
      "j/k/arrows: navigate  h/l: views  PgUp/PgDn: scroll  /: filter  n/N: \
       matches\n\
       a: address  c: concise  r: reload  o: open  p: passes  w: writers  e: \
       export\n\
       [/]: memory region  :: BAP command ($file)  s: script  Tab: next view  \
       q: quit"

let run_pass state name =
  match Project.find_pass name with
  | None -> Error (Error.of_string (sprintf "Unknown pass %s" name))
  | Some pass -> (
      try
        let project = Project.Pass.run_exn pass state.project in
        Ok
          {
            state with
            project;
            functions = functions project;
            status = sprintf "Pass %s completed" name;
            recovered = Hashtbl.Poly.create ();
          }
      with exn -> Error (Error.of_string (Exn.to_string exn)))

let command_args state ?script arguments =
  let expand arguments =
    List.map arguments ~f:(fun argument ->
        if String.equal argument "$file" then state.file else argument)
  in
  match script with
  | Some script -> [ "script"; script; state.file ]
  | None -> (
      match arguments with
      | [] -> [ "disassemble"; state.file ]
      | ("disassemble" | "run") :: _ as arguments ->
          let expanded = expand arguments in
          if List.mem arguments "$file" ~equal:String.equal then expanded
          else expanded @ [ state.file ]
      | arguments -> expand arguments)

let help = text
