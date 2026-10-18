(* prints the lifted x86 instructions as bap mc prints them *)

open Bap.Std

let () = Bap_init.loaded

(* the instructions are at the address 0, which bap mc uses *)

let x86_64 =
  Lifter_test.mode ~addr:0 ~target:"x86_64" ~encoding:"llvm-x86_64" ()

let i686 = Lifter_test.mode ~addr:0 ~target:"i686" ~encoding:"llvm-x86" ()

(* the temporaries, #n, and the let-bound variables, $n, of [bil] renamed
   in the order of their first occurrences, as their numbers are the numbers
   of the variables created before them in the knowledge base *)
let renumber bil =
  let names = Hashtbl.create 16 in
  let numbered name =
    String.length name > 1
    && (name.[0] = '#' || name.[0] = '$')
    && String.for_all Char.Ascii.is_digit
         (String.sub name 1 (String.length name - 1))
  in
  let rename var =
    let name = Var.name var in
    if not (numbered name) then var
    else
      let n =
        match Hashtbl.find_opt names name with
        | Some n -> n
        | None ->
            (* the variables of each kind are numbered apart *)
            let n =
              Hashtbl.fold
                (fun other _ n -> if other.[0] = name.[0] then n + 1 else n)
                names 0
            in
            Hashtbl.add names name n;
            n
      in
      (* a virtual variable is printed with its number, so the renamed one,
         which is only printed, isn't virtual *)
      Var.create ~fresh:false (Printf.sprintf "%c%d" name.[0] n) (Var.typ var)
  in
  Stmt.map
    object
      inherit Stmt.mapper
      method! map_sym = rename
    end
    bil

(* [text] without the underscores that escape the names of the renamed
   variables, which begin with # or $ *)
let unescape text =
  let buf = Buffer.create (String.length text) in
  String.iteri
    (fun i c ->
      let escape =
        c = '_'
        && i + 1 < String.length text
        && (text.[i + 1] = '#' || text.[i + 1] = '$')
      in
      if not escape then Buffer.add_char buf c)
    text;
  Buffer.contents buf

(* prints the assembly and the BIL of the instruction with the encoding
   [code] as bap mc --show-insn=asm --show-bil does, but with the variables
   renumbered *)
let show mode code =
  let insn = Lifter_test.semantics mode code in
  let asm =
    Insn.with_printer "asm" (fun () -> Format.asprintf "%a" Insn.pp insn)
  and bil =
    Bytes.to_string (Bil.to_bytes ~fmt:"pretty" (renumber (Insn.bil insn)))
  in
  print_endline asm;
  print_endline (unescape bil)
