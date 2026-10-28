open Core
open Bap.Std
open Bap_main
open Regular.Std

let symbols =
  Extension.Configuration.parameters Extension.Type.(list string) "symbol"

let concise = Extension.Configuration.flag "concise"

let print symbols concise ppf proj =
  let recovered =
    Bap_decompile.decompile ~concise ~target:(Project.target proj)
      (Project.program proj)
  in
  let recovered =
    if List.is_empty symbols then recovered
    else
      let mangle name =
        "fn_"
        ^ String.map name ~f:(fun c ->
            if Char.is_alphanum c || Char.equal c '_' then c else '_')
      in
      let selected = List.map symbols ~f:mangle in
      {
        recovered with
        functions =
          List.filter recovered.functions ~f:(fun func ->
              List.mem selected func.Bap_decompile.Ast.name ~equal:String.equal);
      }
  in
  Bap_decompile.pp_program ppf recovered

let () =
  Extension.declare ~doc:"decompiles BIR to structured C pseudocode"
    ~provides:[ "decompiler"; "printer" ]
  @@ fun ctxt ->
  let open Extension.Syntax in
  let symbols = List.concat (ctxt --> symbols) in
  let concise = ctxt --> concise in
  let writer = Data.Write.create ~pp:(print symbols concise) () in
  Project.add_writer ~desc:"decompile BIR to C pseudocode" ~ver:Program.version
    "decompile" writer;
  Ok ()
