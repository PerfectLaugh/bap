open Core
open Bap_core_theory
open Bap.Std
open KB.Syntax
include Bap_main.Loggers ()
module Target = Bap_systemz_target
module MC = Disasm_expert.Basic

let make_regs regs =
  let regs =
    List.mapi regs ~f:(fun i r -> (i, r)) |> Map.of_alist_exn (module Int)
  in
  Map.find_exn regs

let registers = make_regs Target.gpr
let regnum s = Scanf.sscanf s "R%d" Fn.id

module Systemz (CT : Theory.Core) = struct
  open Target

  let rec seq = function
    | [] -> CT.perform Theory.Effect.Sort.bot
    | [ x ] -> x
    | x :: xs -> CT.seq x @@ seq xs

  let null = KB.Object.null Theory.Program.cls
  let data xs = CT.blk null (seq xs) (seq [])
  let ( @ ) = CT.append r64

  let reg insn pos =
    match (MC.Insn.ops insn).(pos) with
    | Op.Reg r -> registers (regnum (Reg.name r))
    | _ -> invalid_argf "System z operand %d is not a register" pos ()

  let imm insn pos width =
    match (MC.Insn.ops insn).(pos) with
    | Op.Imm value ->
        Option.value_exn (Imm.to_word value ~width) |> Word.to_bitvec
    | _ -> invalid_argf "System z operand %d is not an immediate" pos ()

  let var insn pos = CT.var (reg insn pos)
  let low insn pos = CT.low r32 (var insn pos)
  let const sort insn pos width = CT.int sort (imm insn pos width)

  let address insn base displacement index =
    let addr = CT.add (var insn base) (const r64 insn displacement 64) in
    match (MC.Insn.ops insn).(index) with
    | Op.Reg r when not (String.equal (Reg.name r) "Nil") ->
        CT.add addr (var insn index)
    | _ -> addr

  let set32 rd value = CT.set rd (CT.high r32 (CT.var rd) @ value)
  let load32 insn = CT.loadw r32 CT.b1 (CT.var mem) (address insn 1 2 3)

  let store32 insn value =
    CT.set mem (CT.storew CT.b1 (CT.var mem) (address insn 1 2 3) value)

  let set_flags left right =
    [ CT.set lt (CT.slt left right); CT.set gt (CT.sgt left right) ]

  let set_result_flags value =
    [
      CT.set lt (CT.msb value);
      CT.set gt (CT.and_ (CT.inv (CT.msb value)) (CT.non_zero value));
    ]

  let move32 insn = data [ set32 (reg insn 0) (low insn 1) ]
  let move64 insn = data [ CT.set (reg insn 0) (var insn 1) ]

  let add64 insn =
    let rd = reg insn 0 in
    let value = CT.add (var insn 0) (CT.signed r64 (const r16 insn 2 16)) in
    data (CT.set rd value :: set_result_flags value)

  let add32 ~immediate insn =
    let rd = reg insn 0 in
    let right =
      if immediate then CT.signed r32 (const r16 insn 2 16) else low insn 2
    in
    let value = CT.add (low insn 1) right in
    data (set32 rd value :: set_result_flags value)

  let load_signed insn =
    data [ CT.set (reg insn 0) (CT.signed r64 (load32 insn)) ]

  let load_unsigned insn = data [ set32 (reg insn 0) (load32 insn) ]
  let store insn = data [ store32 insn (low insn 0) ]

  let store_imm insn =
    let addr = CT.add (var insn 0) (const r64 insn 1 64) in
    data
      [ CT.set mem (CT.storew CT.b1 (CT.var mem) addr (const r32 insn 2 32)) ]

  let compare ~immediate insn =
    let right =
      if immediate then CT.signed r32 (const r16 insn 1 16) else low insn 1
    in
    data (set_flags (low insn 0) right)

  let transfer_range ~store insn =
    let first = regnum (Theory.Var.name (reg insn 0)) in
    let last = regnum (Theory.Var.name (reg insn 1)) in
    let count = last - first + 1 in
    let base = CT.add (var insn 2) (const r64 insn 3 64) in
    let effects =
      List.init count ~f:(fun index ->
          let register = registers (first + index) in
          let addr =
            CT.add base
              (CT.int r64 (Bitvec.M64.int64 (Int64.of_int (index * 8))))
          in
          ( register,
            if store then
              CT.set mem (CT.storew CT.b1 (CT.var mem) addr (CT.var register))
            else CT.set register (CT.loadw r64 CT.b1 (CT.var mem) addr) ))
    in
    let effects =
      if store then effects
      else
        let base = reg insn 2 in
        List.append
          (List.filter effects ~f:(fun (register, _) ->
               not
                 (String.equal (Theory.Var.name register) (Theory.Var.name base))))
          (List.filter effects ~f:(fun (register, _) ->
               String.equal (Theory.Var.name register) (Theory.Var.name base)))
    in
    data (List.map effects ~f:snd)

  let relative insn pc position =
    let displacement = const r64 insn position 64 in
    CT.add (CT.int r64 pc) displacement

  let jump ?condition destination =
    let yes = seq [ CT.goto destination ] in
    let no = seq [] in
    let control =
      match condition with None -> yes | Some c -> CT.branch c yes no
    in
    CT.blk null (seq []) control

  let branch_register insn = CT.blk null (seq []) (seq [ CT.jmp (var insn 0) ])

  let call insn pc return =
    let next =
      match return with Some word -> CT.int r64 word | None -> CT.unk r64
    in
    CT.blk null
      (seq [ CT.set (reg insn 0) next ])
      (seq [ CT.jmp (relative insn pc 1) ])

  let condition name =
    let less = CT.var lt and greater = CT.var gt in
    let either = CT.or_ less greater in
    match name with
    | "JAsmE" -> Some (CT.inv either)
    | "JAsmNE" | "JAsmLH" -> Some either
    | "JAsmH" -> Some greater
    | "JAsmHE" -> Some (CT.inv less)
    | "JAsmL" -> Some less
    | "JAsmLE" -> Some (CT.inv greater)
    | _ -> None

  let lift name insn pc return destination =
    match name with
    | "LR" -> move32 insn
    | "LGR" -> move64 insn
    | "AGHI" -> add64 insn
    | "AR" -> add32 ~immediate:false insn
    | "AHI" -> add32 ~immediate:true insn
    | "LGF" -> load_signed insn
    | "L" -> load_unsigned insn
    | "ST" -> store insn
    | "MVHI" -> store_imm insn
    | "STMG" -> transfer_range ~store:true insn
    | "LMG" -> transfer_range ~store:false insn
    | "CHI" -> compare ~immediate:true insn
    | "CR" -> compare ~immediate:false insn
    | "BRASL" -> call insn pc return
    | "BR" -> branch_register insn
    | "J" -> jump destination
    | "NOPR" -> data []
    | name -> (
        match condition name with
        | Some condition -> jump ~condition destination
        | None ->
            info "unsupported opcode: %s" name;
            data [])
end

let lifter label : unit Theory.eff =
  let lift insn sema = sema >>| fun sema -> Insn.with_basic sema insn in
  Theory.Label.target label >>= fun t ->
  if Theory.Target.belongs Target.parent t then
    KB.collect MC.Insn.slot label >>= function
    | None -> KB.return Insn.empty
    | Some insn ->
        KB.collect Memory.slot label >>= fun memory ->
        let address =
          Option.map memory ~f:(fun mem ->
              Memory.min_addr mem |> Word.to_bitvec)
        in
        let return =
          Option.map address ~f:(fun addr ->
              let next = Int64.(Bitvec.to_int64 addr + 6L) in
              Bitvec.(int64 next mod modulus 64))
        in
        let target =
          match (address, (MC.Insn.ops insn).(0)) with
          | Some pc, Op.Imm displacement ->
              let target =
                Int64.(Bitvec.to_int64 pc + Imm.to_int64 displacement)
              in
              Some Bitvec.(int64 target mod modulus 64)
          | _ -> None
        in
        (match target with
          | Some target -> Theory.Label.for_addr target
          | None -> KB.return (KB.Object.null Theory.Program.cls))
        >>= fun destination ->
        Theory.instance () >>= Theory.require >>= fun (module Core) ->
        let module Systemz = Systemz (Core) in
        lift insn
          (Systemz.lift (MC.Insn.name insn) insn (Option.value_exn address)
             return destination)
  else !!Insn.empty

let load () = KB.promise Theory.Semantics.slot lifter
