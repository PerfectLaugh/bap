#require "bap-primus-unicorn.emu"

module Emu = Bap_emu
module Sym = Emu.Symbolic

let model = function
  | None -> "unsat"
  | Some m ->
      String.concat ","
        (List.map
           (fun (n, v) -> Printf.sprintf "%s=%Lx" n (Int64.logand v 0xffL))
           m)

let () =
  let file, stdin =
    match Bap_script.args () with
    | [ file; stdin ] -> (file, stdin)
    | _ -> failwith "expected FILE INPUT"
  in
  let emu =
    Emu.create ~components:Sym.components
      ~redirects:[ ("<stdin>", stdin) ]
      (Bap_script.project file)
  in
  (match Emu.run emu ~until:0x693L with
  | Paused -> ()
  | _ -> failwith "getchar didn't return");
  Sym.symbolize emu (Reg "RAX");
  Printf.printf "RAX %s, RBX %s\n%!"
    (String.concat ","
       (List.map (Option.value ~default:"-") (Sym.formula emu (Reg "RAX"))))
    (String.concat ","
       (List.map (Option.value ~default:"-") (Sym.formula emu (Reg "RBX"))));
  let branches = ref [] in
  Sym.on_branch emu (fun _ b -> branches := b :: !branches);
  ignore (Emu.run emu);
  List.iter
    (fun b ->
      Printf.printf "branch %Lx %b flips with %s\n" (Sym.addr b) (Sym.taken b)
        (model (Sym.flip b)))
    (List.rev !branches)
