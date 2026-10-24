#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

(* The project of the memory of the paused program, see Emu.project: of
   echo at main, with the subroutines of its symbols, with the patched
   instruction, as the program has it, and of mprotect, when it reaches
   the code, that it wrote to its buffer, which the script names, so
   that it is disassembled. *)

let show proj =
  let subs = Term.enum sub_t (Project.program proj) |> Seq.to_list in
  printf "%d subs, %d with code:" (List.length subs)
    (List.count subs ~f:(fun s -> Term.length blk_t s > 0));
  List.iter subs ~f:(fun s ->
      match Term.get_attr s address with
      | Some a when Term.length blk_t s > 0 ->
          printf " %s@%s" (Sub.name s) (Addr.string_of_value a)
      | _ -> ());
  print_endline ""

(* the expression in a line, as the printer breaks the long ones *)
let exp e =
  Exp.to_string e |> String.split_lines |> List.map ~f:String.strip
  |> String.concat ~sep:" "

let () =
  match Bap_script.args () with
  | [ echo; mprotect ] ->
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
      ignore (Emu.run emu ~until:0x40076bL : Emu.status);
      let regions = Emu.regions emu in
      printf "regions: %d, the file:%s\n" (List.length regions)
        (List.filter regions ~f:(fun (r : Emu.region) ->
             Int64.(r.lower < 0x700000L))
        |> List.map ~f:(fun (r : Emu.region) ->
            sprintf " %Lx-%Lx %s%s%s" r.lower r.upper
              (if r.readable then "r" else "-")
              (if r.writable then "w" else "-")
              (if r.executable then "x" else "-"))
        |> String.concat);
      let proj = Emu.project emu in
      show proj;
      (* the file's bytes, mov $0xa, %edi, and the patched ones, mov
         $0x2b, %edi, are in the projects *)
      let def proj =
        Term.enum sub_t (Project.program proj)
        |> Seq.concat_map ~f:(Term.enum blk_t)
        |> Seq.concat_map ~f:(Term.enum def_t)
        |> Seq.find ~f:(fun d ->
            Option.exists (Term.get_attr d address)
              ~f:(Addr.equal (Addr.of_int64 0x400727L)))
        |> Option.value_map ~default:"none" ~f:(fun d ->
            (* without the tid, which isn't stable *)
            sprintf "%s := %s" (Var.name (Def.lhs d)) (exp (Def.rhs d)))
      in
      printf "400727: %s\n" (def proj);
      Emu.write emu 0x400727L "\xbf\x2b";
      printf "patched 400727: %s\n" (def (Emu.project emu));
      let code = 0x405000L in
      let emu = Emu.create (Bap_script.project mprotect) in
      ignore (Emu.run emu ~until:code : Emu.status);
      Emu.add_symbol emu "written" code;
      let proj = Emu.project emu in
      show proj;
      let written =
        Term.enum sub_t (Project.program proj)
        |> Seq.find_exn ~f:(fun s -> String.equal (Sub.name s) "written")
      in
      (* the defs of the registers, as the temporaries are numbered by
         the run *)
      Term.enum blk_t written
      |> Seq.iter ~f:(fun b ->
          Term.enum def_t b
          |> Seq.iter ~f:(fun d ->
              if Var.is_physical (Def.lhs d) then
                printf "  %s := %s\n" (Var.name (Def.lhs d)) (exp (Def.rhs d))))
  | _ -> failwith "expected ECHO MPROTECT"
