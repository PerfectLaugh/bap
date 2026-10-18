open Core
open Bap_core_theory
open Bap.Std
open KB.Syntax
module Dis = Disasm_expert.Basic

(* the target and the encoding are looked up when they are first used,
   as the modes are created before the plugins that declare them are
   loaded *)
type mode = {
  target_ : Theory.Target.t Lazy.t;
  encoding_ : Theory.Language.t Lazy.t;
  addr : int;
  typ : string -> Type.t option;
}

let mode ?(typ = fun _ -> None) ?(addr = 0x10000) ~target ~encoding () =
  {
    target_ = lazy (Theory.Target.get ~package:"bap" target);
    encoding_ = lazy (Theory.Language.read ~package:"bap" encoding);
    addr;
    typ;
  }

let target { target_ } = Lazy.force target_
let encoding { encoding_ } = Lazy.force encoding_
let bits mode = Theory.Target.bits (target mode)

let endian mode =
  if Theory.Endianness.(equal le) (Theory.Target.endianness (target mode)) then
    LittleEndian
  else BigEndian

let bytes_of_hex code =
  String.split code ~on:' '
  |> List.filter ~f:(Fn.non String.is_empty)
  |> List.map ~f:(fun b -> Char.of_int_exn (Int.of_string ("0x" ^ b)))
  |> String.of_char_list

let new_insn mode mem insn =
  KB.Object.create Theory.Program.cls >>= fun code ->
  (* one unit for each target, as the target of a unit is fixed *)
  let name = Theory.Target.to_string (target mode) in
  KB.Symbol.intern name Theory.Unit.cls >>= fun unit ->
  KB.provide Theory.Unit.target unit (target mode) >>= fun () ->
  KB.provide Theory.Label.encoding code (encoding mode) >>= fun () ->
  KB.provide Theory.Label.addr code (Some (Bitvec.M64.int mode.addr))
  >>= fun () ->
  KB.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) @@ fun () ->
  KB.provide Memory.slot code (Some mem) >>= fun () ->
  KB.provide Dis.Insn.slot code (Some insn) >>= fun () ->
  KB.collect Theory.Semantics.slot code >>| fun _ -> code

let semantics mode code =
  let data = Bigstring.of_string (bytes_of_hex code) in
  let base = Addr.of_int ~width:(bits mode) mode.addr in
  let mem = Or_error.ok_exn (Memory.create (endian mode) base data) in
  let dis = Or_error.ok_exn (Dis.lookup (target mode) (encoding mode)) in
  let insn =
    match Dis.insn_of_mem dis mem with
    | Ok (_, Some insn, _) -> insn
    | Ok (_, None, _) -> failwithf "%s: not an instruction" code ()
    | Error err -> failwithf "%s: %s" code (Error.to_string_hum err) ()
  in
  match Toplevel.try_eval Theory.Semantics.slot (new_insn mode mem insn) with
  | Error conflict ->
      failwithf "%s: the lifters failed: %s" code
        (Format.asprintf "%a" KB.Conflict.pp conflict)
        ()
  | Ok sema -> sema

let lift mode code = Insn.bil (semantics mode code)

(* A call to an intrinsic function is a special statement, the semantics
   of the intrinsic is the semantics of the label with its name, which is
   inlined, so that the evaluation includes it. The calls of the intrinsics
   without semantics, such as breakpoints, are kept. *)
let intrinsic_call = "@attribute:(bap:call intrinsic:"

let called_intrinsic = function
  | Bil.Special s when String.is_prefix s ~prefix:intrinsic_call ->
      Some
        ("intrinsic:"
        ^ String.chop_suffix_exn ~suffix:")"
            (String.drop_prefix s (String.length intrinsic_call)))
  | _ -> None

let intrinsic_semantics mode name =
  Theory.Label.for_name name >>= fun label ->
  let unit = Theory.Target.to_string (target mode) in
  KB.Symbol.intern unit Theory.Unit.cls >>= fun unit ->
  KB.provide Theory.Unit.target unit (target mode) >>= fun () ->
  KB.promising Theory.Label.unit ~promise:(fun _ -> !!(Some unit)) @@ fun () ->
  KB.collect Theory.Semantics.slot label >>| fun _ -> label

let rec inline_intrinsics mode bil =
  List.concat_map bil ~f:(fun stmt ->
      match called_intrinsic stmt with
      | Some name -> (
          match
            Toplevel.try_eval Theory.Semantics.slot
              (intrinsic_semantics mode name)
          with
          | Ok sema when not (List.is_empty (Insn.bil sema)) -> Insn.bil sema
          | _ -> [ stmt ])
      | None -> (
          match stmt with
          | Bil.If (c, yes, no) ->
              [
                Bil.If (c, inline_intrinsics mode yes, inline_intrinsics mode no);
              ]
          | Bil.While (c, body) ->
              [ Bil.While (c, inline_intrinsics mode body) ]
          | stmt -> [ stmt ]))

let lift mode code = inline_intrinsics mode (lift mode code)

let typ mode name =
  match Theory.Target.var (target mode) name with
  | Some v -> Var.typ (Var.reify v)
  | None -> (
      match mode.typ name with Some t -> t | None -> Type.imm (bits mode))

let width_of_var v =
  match Var.typ v with Type.Imm w -> w | _ -> failwith "not a register"

(* the variables are created once for each target, as their creation
   validates the names *)
let vars = Hashtbl.create (module String)

let cached mode name create =
  let key = Theory.Target.to_string (target mode) ^ ":" ^ name in
  Hashtbl.find_or_add vars key ~default:create

let mem mode =
  cached mode "mem" @@ fun () ->
  let data = Theory.Target.data (target mode) in
  let v = Var.reify data in
  Var.create (Var.name v) (Var.typ v)

let word width value = Word.create (Bitvec.of_string value) width

type location =
  | Reg of var
  | Mem of int * int  (** the number of bytes and the address *)
  | Pc

let location mode name =
  match String.lsplit2 name ~on:'@' with
  | Some (n, a) when String.is_prefix n ~prefix:"M" ->
      Mem (Int.of_string (String.drop_prefix n 1), Int.of_string a)
  | _ when String.equal name "PC" -> Pc
  | _ -> Reg (cached mode name @@ fun () -> Var.create name (typ mode name))

let size_of_bytes n = Size.of_int_exn (8 * n)

(* the statement that stores [value] in the location [name] *)
let initialize mode (name, value) =
  match location mode name with
  | Reg v -> Bil.(v := int (word (width_of_var v) value))
  | Mem (n, a) ->
      let mem = mem mode in
      let addr = Word.of_int ~width:(bits mode) a in
      let value = word (8 * n) value in
      Bil.(
        mem :=
          store ~mem:(var mem) ~addr:(int addr) (int value) (endian mode)
            (size_of_bytes n))
  | Pc -> failwith "PC can't be initialized"

let pp_bindings xs =
  String.concat ~sep:" " (List.map xs ~f:(fun (n, v) -> n ^ "=" ^ v))

let debug code =
  match Sys.getenv "LIFTER_TEST_DEBUG" with
  | Some _ -> Format.asprintf "@\n%a" Bil.pp code
  | None -> ""

let check_typed asm bil =
  match Type.check bil with
  | Ok () -> ()
  | Error err ->
      OUnit2.assert_failure
        (sprintf "%s: the lifted code is not well-typed: %s%s" asm
           (Type.Error.to_string err) (debug bil))

(* the program that evaluates the instruction [code] with the inputs
   [init], and the expected outputs *)
let prepare mode code (init, expect) =
  let bil = List.map init ~f:(initialize mode) @ code in
  (* the expected memory words are loaded into fresh variables *)
  let loads, expect =
    List.fold_map expect ~init:[] ~f:(fun loads (name, value) ->
        match location mode name with
        | Mem (n, a) ->
            let v = Var.create ~fresh:true "word" (Type.imm (8 * n)) in
            let mem = mem mode in
            let addr = Word.of_int ~width:(bits mode) a in
            let load =
              Bil.(
                v :=
                  load ~mem:(var mem) ~addr:(int addr) (endian mode)
                    (size_of_bytes n))
            in
            (load :: loads, (name, Reg v, value))
        | loc -> (loads, (name, loc, value)))
  in
  (bil @ List.rev loads, expect)

(* [size] is the size of the instruction, so that PC is the address of the
   next instruction if the instruction doesn't jump *)
let check mode asm ~size code (init, _) expect state =
  List.iter expect ~f:(fun (name, loc, value) ->
      let got, width =
        match loc with
        | Reg v -> (Lifter_test_eval.lookup state v, width_of_var v)
        | Pc ->
            let next = Word.of_int ~width:(bits mode) (mode.addr + size) in
            ( Some (Option.value (Lifter_test_eval.pc state) ~default:next),
              bits mode )
        | Mem _ -> assert false
      in
      let expected = word width value in
      match got with
      | Some got when Word.equal got expected -> ()
      | got ->
          OUnit2.assert_failure
            (sprintf "%s [%s]: %s is %s, expected %s%s" asm (pp_bindings init)
               name
               (Option.value_map got ~default:"not set" ~f:Word.to_string)
               (Word.to_string expected) (debug code)))

(* The labels of the addresses are shared by the targets, e.g., the label
   of a branch destination, so each target has its own knowledge base,
   which starts as the knowledge base before the first test. The knowledge
   base after the first test of a target, which has the Lisp program of
   the target, is the knowledge base of the following tests, which don't
   keep what they add to it, so that it doesn't grow with each test. *)
let initial_state = lazy (Toplevel.current ())
let states = Hashtbl.create (module String)

let with_state_of mode f =
  let name = Theory.Target.to_string (target mode) in
  match Hashtbl.find states name with
  | Some state ->
      Toplevel.set state;
      f ()
  | None ->
      Toplevel.set (Lazy.force initial_state);
      Exn.protect ~f ~finally:(fun () ->
          Hashtbl.set states ~key:name ~data:(Toplevel.current ()))

let case mode asm code vectors =
  OUnit2.( >:: ) asm @@ fun _ctxt ->
  with_state_of mode @@ fun () ->
  let bil = lift mode code in
  let size = String.length (bytes_of_hex code) in
  (* the code and the inputs are typed once, the inputs of the vectors
     have the same types *)
  (match vectors with
  | (init, _) :: _ -> check_typed asm (List.map init ~f:(initialize mode) @ bil)
  | [] -> check_typed asm bil);
  List.iter vectors ~f:(fun vector ->
      let program, expect = prepare mode bil vector in
      check mode asm ~size bil vector expect (Lifter_test_eval.eval program))

let bindings s =
  String.split s ~on:' '
  |> List.filter ~f:(Fn.non String.is_empty)
  |> List.map ~f:(fun b ->
      match String.lsplit2 b ~on:'=' with
      | Some (n, v) -> (n, v)
      | None -> failwithf "%s: expected name=value" b ())

let vectors s =
  String.split_lines s
  |> List.filter ~f:(fun l -> not (String.is_empty (String.strip l)))
  |> List.map ~f:(fun l ->
      match String.lsplit2 l ~on:'|' with
      | Some (init, expect) -> (bindings init, bindings expect)
      | None -> failwithf "%s: expected inputs | outputs" l ())
