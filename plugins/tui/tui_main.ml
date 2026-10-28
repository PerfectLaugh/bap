open Core
open Bap_main
open Bap_core_theory

type Extension.Error.t += Fail of string

let concise = Extension.Command.flag "concise"
let dump = Extension.Command.flag "dump"

let loader =
  Extension.Command.parameter Extension.Type.(string =? "llvm") "loader"

let target =
  let typ =
    Extension.Type.define Theory.Target.unknown ~name:"NAME"
      ~digest:(fun target ->
        Stdlib.Digest.string (Theory.Target.to_string target))
      ~parse:(fun name ->
        match Theory.Target.lookup ~package:"bap" name with
        | Some target -> target
        | None -> invalid_argf "unknown target %S" name ())
      ~print:Theory.Target.to_string
  in
  Extension.Command.parameter typ "target"

let file =
  Extension.Command.argument Extension.Type.("FILE" %: string =? "a.out")

let run concise dump loader target file =
  match Tui_model.load ~concise ~loader ~target file with
  | Error error -> Error (Fail (Error.to_string_hum error))
  | Ok state ->
      if dump then (
        print_string (Tui_view.dump state);
        Ok ())
      else
        Tui_action.run state
        |> Result.map_error ~f:(fun message -> Fail message)

let () =
  let requires =
    [
      "semantics";
      "function-starts";
      "disassembler";
      "lifter";
      "symbolizer";
      "rooter";
      "reconstructor";
      "brancher";
      "loader";
      "abi";
    ]
  in
  Extension.Command.(
    declare ~doc:"interactive BAP terminal workspace" ~requires "tui"
      (args $ concise $ dump $ loader $ target $ file))
  @@ fun concise dump loader target file _ctxt ->
  run concise dump loader target file
