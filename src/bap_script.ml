open Core
open Bap.Std

let arguments = ref []
let set_args args = arguments := args
let args () = !arguments
let initialized = ref false

(* the options of the libraries of the script, e.g., of the debugger *)
let required = ref []
let require_options options = required := !required @ options

let fail fmt =
  Format.kasprintf
    (fun msg ->
      Format.eprintf "bap script: %s@." msg;
      Stdlib.exit 1)
    fmt

(* the options are of the command ".", which does nothing, see
   bap_frontend.ml, so that bap only loads the plugins *)
let init ?(options = []) () =
  if !initialized then fail "bap is already initialized";
  initialized := true;
  match
    Bap_main.init ~name:"bap"
      ~argv:(Array.of_list (("bap" :: "." :: !required) @ options))
      ()
  with
  | Ok () -> ()
  | Error (Bap_main.Extension.Error.Exit_requested code) -> Stdlib.exit code
  | Error err -> fail "%a" Bap_main.Extension.Error.pp err

let run pass proj =
  match Project.Pass.run pass proj with
  | Ok proj -> proj
  | Error (Runtime_error (_, exn)) ->
      fail "the pass %s failed: %s" (Project.Pass.name pass) (Exn.to_string exn)
  | Error (Unsat_dep (_, dep)) ->
      fail "the pass %s depends on the unknown pass %s" (Project.Pass.name pass)
        dep

(* the default loader of the disassemble command, which runs the passes
   that are flagged with autorun, e.g., the api pass, first *)
let project ?(loader = "llvm") ?target file =
  if not !initialized then init ();
  match Project.create (Project.Input.load ~loader ?target file) with
  | Error err -> fail "can't load %s: %a" file Error.pp err
  | Ok proj ->
      Project.passes ()
      |> List.filter ~f:Project.Pass.autorun
      |> List.fold ~init:proj ~f:(Fn.flip run)

let run_pass name proj =
  match Project.find_pass name with
  | None -> fail "unknown pass %s" name
  | Some pass -> run pass proj
