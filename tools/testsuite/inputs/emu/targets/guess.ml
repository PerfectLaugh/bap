#require "bap-primus-native.emu"

module Emu = Bap_emu
module Sym = Emu.Symbolic

let model = function
  | None -> "unsat"
  | Some m ->
      String.concat ","
        (List.map
           (fun (n, v) -> Printf.sprintf "%s=%Lx" n (Int64.logand v 0xffL))
           m)

let formulas emu place =
  String.concat ","
    (List.map (function Some f -> f | None -> "-") (Sym.formula emu place))

let status = function
  | Emu.Exited c ->
      Printf.sprintf "exited %s"
        (match c with Some c -> string_of_int c | None -> "?")
  | Paused -> "paused"
  | Running -> "running"
  | Failed m -> "failed " ^ m

let () =
  match Bap_script.args () with
  | file :: input :: until :: reg :: api ->
      let emu =
        Emu.create ~components:Sym.components
          ~redirects:[ ("<stdin>", input) ]
          (Bap_script.project ~disassemble:true ~api file)
      in
      (match Emu.run emu ~until:(Int64.of_string until) with
      | Paused -> ()
      | s -> failwith ("getchar didn't return: " ^ status s));
      Printf.printf "before: %s\n%!" (formulas emu (Reg reg));
      (try Sym.symbolize emu (Reg "NO-SUCH-REGISTER")
       with Invalid_argument _ -> print_endline "rejects the unknown register");
      Sym.symbolize emu (Reg reg);
      Printf.printf "after: %s\n%!" (formulas emu (Reg reg));
      Printf.printf "unsolved: %s\n%!" (model (Sym.solve emu));
      let branches = ref [] in
      Sym.on_branch emu (fun emu b ->
          (try Sym.symbolize emu (Reg reg)
           with Invalid_argument _ -> print_endline "rejects the hook");
          branches := b :: !branches);
      let s = status (Emu.run emu) in
      Printf.printf "%s\n" s;
      List.iter
        (fun b ->
          Printf.printf "branch %Lx %s flips with %s\n" (Sym.addr b)
            (if Sym.taken b then "taken" else "fell")
            (model (Sym.flip b)))
        (List.rev !branches);
      Printf.printf "branches %d\n" (List.length !branches);
      Printf.printf "solved: %s\n" (model (Sym.solve emu));
      Printf.printf "ended: %s\n" (formulas emu (Reg reg))
  | _ -> failwith "expected FILE INPUT UNTIL REG [API]"
