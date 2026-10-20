open Core
open Bap_main
open Bap_knowledge
open Bap_core_theory
open Bap.Std
open KB.Syntax
include Loggers ()

(* the commands are in the direct style, see [KB.direct] *)

let read_name name =
  let package = KB.await KB.Symbol.package in
  KB.Name.to_string (KB.Name.read ~package name)

let print_semantics label slots =
  let sema = KB.await (KB.collect Theory.Semantics.slot label) in
  match List.map slots ~f:read_name with
  | [] -> Format.printf "%a@\n" KB.Value.pp sema
  | slots -> Format.printf "%a@\n" (KB.Value.pp_slots slots) sema

let require prop label has =
  match KB.await (KB.collect prop label) with None -> false | Some p -> has p

let belongs_to_unit unit insn =
  match unit with
  | None -> true
  | Some unit ->
      require Theory.Label.unit insn @@ fun unit' ->
      Theory.Unit.equal unit unit'

let belongs_to_subr subr insn =
  match subr with
  | None -> true
  | Some subr ->
      require Theory.Label.addr subr @@ fun subr ->
      require Theory.Label.unit insn @@ fun unit ->
      require Theory.Label.addr insn @@ fun insn ->
      let target = KB.await (KB.collect Theory.Unit.target unit) in
      let bits = Theory.Target.code_addr_size target in
      let state = KB.await (KB.collect Project.State.slot unit) in
      let subrs = Project.State.subroutines state in
      let insn = Word.create insn bits and subr = Word.create subr bits in
      Disasm.Subroutines.belongs subrs ~entry:subr insn

let find_entry subrs name_or_addr =
  Disasm.Subroutines.entries subrs
  |> Set.to_sequence
  |> Seq.find ~f:(fun addr ->
      let addr = Word.to_bitvec addr in
      Poly.(Bitvec.to_string addr = name_or_addr)
      ||
      let label = KB.await (Theory.Label.for_addr addr) in
      match KB.await (KB.collect Theory.Label.name label) with
      | None -> false
      | Some name -> String.equal name name_or_addr)

(* the callbacks of the monadic functions run outside of [KB.direct] *)
let iter_subr entry subrs disasm ~f =
  KB.await
  @@ Disasm.Driver.explore disasm ~entry ~init:()
       ~follow:(fun next ->
         KB.return @@ Disasm.Subroutines.belongs subrs ~entry next)
       ~block:(fun _mem -> Disasm.Driver.execution_order)
       ~node:(fun insns () -> KB.direct @@ fun () -> List.iter insns ~f)
       ~edge:(fun _ _ _ -> KB.return ())

let print_unit () =
  KB.await (KB.objects Theory.Unit.cls)
  |> Seq.iter ~f:(fun obj ->
      let str = KB.await (KB.Object.repr Theory.Unit.cls obj) in
      let triple = KB.await (KB.collect Theory.Unit.target obj) in
      Format.printf "%-40s %a@\n" str Theory.Target.pp triple)

let in_package package f =
  match package with
  | None -> f ()
  | Some package ->
      KB.await (KB.Symbol.in_package package @@ fun () -> KB.direct f)

let print_insn ?package slots obj =
  in_package package @@ fun () ->
  let str = KB.await (KB.Object.repr Theory.Program.cls obj) in
  Format.printf "%s@\n" str;
  Option.iter slots ~f:(print_semantics obj)

let list_insns unit slots =
  KB.await (KB.objects Theory.Program.cls)
  |> Seq.iter ~f:(fun obj ->
      if belongs_to_unit unit obj then print_insn slots obj)

let print_subr unit name_or_addr slots =
  let state = KB.await (KB.collect Project.State.slot unit) in
  let current = KB.await KB.Symbol.package in
  let package = KB.await (KB.collect Theory.Unit.path unit) in
  in_package package @@ fun () ->
  let sub = Project.State.subroutines state
  and dis = Project.State.disassembly state in
  match find_entry sub name_or_addr with
  | None -> ()
  | Some entry -> iter_subr entry sub dis ~f:(print_insn ~package:current slots)

let matches name filter =
  match filter with
  | None -> true
  | Some prefix -> String.is_prefix ~prefix name

let is_subroutine obj = require Theory.Label.is_subroutine obj Fn.id

let list_subrs unit filter =
  KB.await (KB.objects Theory.Program.cls)
  |> Seq.iter ~f:(fun obj ->
      if belongs_to_unit unit obj && is_subroutine obj then
        let str = KB.await (KB.Object.repr Theory.Program.cls obj) in
        match KB.await (KB.collect Theory.Label.name obj) with
        | None when Option.is_none filter ->
            Format.printf "%s: unresolved@\n" str
        | Some name when matches name filter ->
            Format.printf "%s: %s\n" str name
        | _ -> ())

let register () =
  let open Project.Analysis in
  let package = "bap" in

  register ~package "instruction"
    (args program $ rest string)
    (fun label slots -> KB.direct @@ fun () -> print_semantics label slots)
    ~desc:
      "Prints the instruction semantics. Prints the semantics of an \
       instruction with the given label. If no fields are specified, then \
       prints all properties in the semantics object. Otherwise, prints only \
       the specified fields.";

  register ~package "instructions"
    (args @@ keyword "unit" unit $ keyword "semantics" (rest string))
    (fun unit slots -> KB.direct @@ fun () -> list_insns unit slots)
    ~desc:
      "Prints all instructions. If :unit is specified then prints only \
       instructions that belong to that unit. If :semantics is specified then \
       prints the semantics of each instruction. The :semantics keyword could \
       be followed by one or more field names. If no fields are specified, \
       then all properties of an instruction will be printed, otherwise only \
       those that are specified will be printed.";

  register ~package "units" (args empty)
    (fun () -> KB.direct print_unit)
    ~desc:"Prints all units. Prints all units stored in the knowledge base.";

  register ~package "subroutines"
    (args @@ keyword "unit" unit $ keyword "matches" string)
    (fun unit filter -> KB.direct @@ fun () -> list_subrs unit filter)
    ~desc:
      "Prints all subroutines. If :unit is specified, then prints only \
       subroutines of that unit. If :matches is specified, then prints only \
       subroutines that match the name.";

  register ~package "subroutine"
    (args @@ unit $ string $ keyword "semantics" (rest string))
    (fun unit name slots -> KB.direct @@ fun () -> print_subr unit name slots)
    ~desc:
      "Prints a subroutine. Prints the subroutine in the specified unit with \
       the given name or address. If :semantics is specified, then prints the \
       semantics of each instruction. The :semantics keyword could be followed \
       by one or more field names. If no fields are specified, then all \
       properties of an instruction will be printed, otherwise only those that \
       are specified will be printed."
