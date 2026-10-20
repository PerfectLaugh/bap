open Core
open Bap.Std
open Bap_core_theory

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

(* the symbols of the knowledge base, e.g., provided with
   --read-symbols-from, as the subroutine terms of the bare program, so
   that the components that need the program work without the
   disassembly, e.g., the Lisp machine, which links the stubs by the
   names and addresses of their subroutines *)
let synthesize_program proj =
  match Project.get proj filename with
  | None -> proj
  | Some file -> (
      let result = Toplevel.var "bare-symbols" in
      Toplevel.put result
        (let open KB.Syntax in
         Theory.Unit.for_file file >>= fun unit ->
         KB.collect Theory.Unit.subroutines unit >>= fun starts ->
         Set.to_list starts
         |> KB.List.fold ~init:String.Map.empty ~f:(fun symbols addr ->
             Theory.Label.for_addr addr >>= fun label ->
             (* the fresh label has no unit, which the symbol
                   providers need, e.g., to find the symbols of the
                   file that the label is in *)
             KB.provide Theory.Label.unit label (Some unit) >>= fun () ->
             KB.collect Theory.Label.name label >>= fun name ->
             (match name with
               | Some _ -> KB.return name
               | None -> KB.resolve Theory.Label.possible_name label)
             >>| function
             | None -> symbols
             | Some name -> Map.set symbols ~key:name ~data:addr));
      match Toplevel.get result with
      | symbols when Map.is_empty symbols -> proj
      | symbols ->
          (* the external functions are subroutines without addresses, so
             that the Lisp machine finds their prototypes, e.g., from the
             api files, and links their stubs, which the GOT slots of the
             program are then patched to; the well-known data objects of
             libc are excepted, as their slots must keep their values *)
          let data_objects =
            String.Set.of_list
              [
                "environ";
                "__environ";
                "__sF";
                "__progname";
                "program_invocation_name";
                "program_invocation_short_name";
                "optarg";
                "optind";
                "opterr";
                "optopt";
                "stdin";
                "stdout";
                "stderr";
                "__stack_chk_guard";
                "__page_size";
                "__ctype_b";
                "__ctype_tolower";
                "__ctype_toupper";
              ]
          in
          let imports =
            match
              Ogre.eval
                (Ogre.collect
                   Ogre.Query.(select (from Image.Scheme.external_reference)))
                (Project.specification proj)
            with
            | Error _ -> []
            | Ok refs ->
                Seq.to_list refs
                |> List.filter_map ~f:(fun (_, name) ->
                    if Set.mem data_objects name || Map.mem symbols name then
                      None
                    else Some name)
                |> List.dedup_and_sort ~compare:String.compare
          in
          let width = Theory.Target.bits (Project.target proj) in
          let subs =
            List.map imports ~f:(fun name -> Sub.create ~name ())
            @ List.map (Map.to_alist symbols) ~f:(fun (name, addr) ->
                Term.set_attr (Sub.create ~name ()) address
                  (Word.create addr width))
          in
          Project.with_program proj (Program.create ~subs ()))

(* the default loader of the disassemble command, which runs the passes
   that are flagged with autorun, e.g., the api pass, first; with [~bare]
   the disassembly and the lifting are skipped, for the executors that
   run the code natively *)
let project ?(bare = false) ?(loader = "llvm") ?target file =
  if not !initialized then init ();
  let state = if bare then Some Project.empty_state else None in
  match Project.create ?state (Project.Input.load ~loader ?target file) with
  | Error err -> fail "can't load %s: %a" file Error.pp err
  | Ok proj ->
      let proj = if bare then synthesize_program proj else proj in
      Project.passes ()
      |> List.filter ~f:Project.Pass.autorun
      |> List.fold ~init:proj ~f:(Fn.flip run)

let run_pass name proj =
  match Project.find_pass name with
  | None -> fail "unknown pass %s" name
  | Some pass -> run pass proj
