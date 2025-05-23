open Core
open Bap.Std

open Powerpc_types

module Model = Powerpc_model

module Std = struct

  open Powerpc_rtl

  include Powerpc_utils
  include Powerpc_cpu
  include Powerpc_dsl
  include Powerpc_types

  module RTL = struct
    include Powerpc_rtl
    include Infix
    let foreach = foreach ~inverse:true
  end

  type rtl = RTL.rtl [@@deriving bin_io, compare, sexp]
  type exp = RTL.exp [@@deriving bin_io, compare, sexp]
  type lift = cpu -> op array -> rtl list

  let bil_of_rtl = RTL.bil_of_t

  let concat f g = fun cpu ops -> f cpu ops @ g cpu ops

  let (^) = concat

  let dot fc cpu ops =
    let res = signed cpu.reg ops.(0) in
    let x = signed var cpu.word_width in
    fc cpu ops @
    RTL.[
      x := low cpu.word_width res;
      nth bit cpu.cr 0 := x < zero;
      nth bit cpu.cr 1 := x > zero;
      nth bit cpu.cr 2 := x = zero;
    ]

  let lifters = String.Table.create ()

  let register name lifter =
    Hashtbl.change lifters name ~f:(fun _ -> Some lifter)


  (* see https://reviews.llvm.org/D70758  *)
  let rename_dot_to_rec old =
    String.(chop_suffix_exn old ~suffix:"o" ^ "_rec")


  let register_dot name lifter =
    List.iter ~f:(fun name -> register name (dot lifter)) [
      name;
      rename_dot_to_rec name;
    ]


  let (>|) = register
  let (>.) = register_dot

  let lift addr_size endian mem insn =
    let insn = Insn.of_basic insn in
    let cpu = make_cpu addr_size endian mem  in
    let lift lifter =
      try
        lifter cpu (Insn.ops insn) |>
        bil_of_rtl |>
        Result.return
      with
      | Failure str -> Error (Error.of_string str) in
    match Hashtbl.find lifters (Insn.name insn) with
    | None -> Ok []
    | Some lifter -> lift lifter

  module T32 = struct
    module CPU = Model.PowerPC_32_cpu
    let lift = lift `r32 BigEndian
  end

  module T64 = struct
    module CPU = Model.PowerPC_64_cpu
    let lift = lift `r64 BigEndian
  end

  module T64_le = struct
    module CPU = Model.PowerPC_64_cpu
    let lift = lift `r64 LittleEndian
  end

  include Model

end
