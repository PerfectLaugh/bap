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
         |> KB.List.filter_map ~f:(fun addr ->
             Theory.Label.for_addr addr >>= fun label ->
             (* the fresh label has no unit, which the symbol
                providers need, e.g., to find the symbols of the file
                that the label is in, and the label, that has one,
                e.g., of another file at the same address, keeps it *)
             ( KB.collect Theory.Label.unit label >>= function
               | Some _ -> KB.return ()
               | None -> KB.provide Theory.Label.unit label (Some unit) )
             >>= fun () ->
             KB.collect Theory.Label.name label >>= fun name ->
             (match name with
               | Some _ -> KB.return name
               | None -> KB.resolve Theory.Label.possible_name label)
             >>| Option.map ~f:(fun name -> (name, addr))));
      (* the subroutines are by their addresses, as the names of the
         static functions of different files may be the same *)
      match Toplevel.get result with
      | symbols ->
          (* the external functions are subroutines without addresses, so
             that the Lisp machine finds their prototypes, e.g., from the
             api files, and links their stubs, which the GOT slots of the
             program are then patched to; the well-known data objects of
             libc are excepted, as their slots must keep their values *)
          let defined = String.Set.of_list (List.map symbols ~f:fst) in
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
                    (* the version of the symbol, e.g., @@GLIBC_2.0, is
                       not of the name of the function *)
                    let name =
                      match String.lsplit2 name ~on:'@' with
                      | Some (name, _) -> name
                      | None -> name
                    in
                    if Set.mem data_objects name || Set.mem defined name then
                      None
                    else Some name)
                |> List.dedup_and_sort ~compare:String.compare
          in
          let width = Theory.Target.bits (Project.target proj) in
          (* the terms are named as the subroutines, which the
             disassembly finds, e.g., for the variables of their
             addresses, that the Primus loader defines *)
          let sub name =
            let tid = Tid.create () in
            Tid.set_name tid name;
            Sub.create ~tid ~name ()
          in
          (* the entry point, which the stripped program may have no
             symbol for, is named as the disassembly names it *)
          let entry =
            match
              Ogre.eval
                (Ogre.request Image.Scheme.entry_point)
                (Project.specification proj)
            with
            | Ok (Some addr) ->
                (* the lower bit of the entry of ARM is the Thumb state *)
                let addr =
                  match Project.arch proj with
                  | #Arch.arm | #Arch.thumb -> Int64.(addr land lnot 1L)
                  | _ -> addr
                in
                Some Bitvec.(int64 addr mod modulus width)
            | _ -> None
          in
          let symbols =
            match entry with
            | Some addr
              when not
                     (List.exists symbols ~f:(fun (_, x) -> Bitvec.equal x addr))
              ->
                ( sprintf "sub_%s"
                    (Bitvec.to_string addr
                    |> String.chop_prefix_if_exists ~prefix:"0x"),
                  addr )
                :: symbols
            | _ -> symbols
          in
          let subs =
            List.map imports ~f:sub
            @ List.map symbols ~f:(fun (name, addr) ->
                let sub =
                  Term.set_attr (sub name) address (Word.create addr width)
                in
                match entry with
                | Some entry when Bitvec.equal entry addr ->
                    Term.set_attr sub Sub.entry_point ()
                | _ -> sub)
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
