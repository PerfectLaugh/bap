(** The static slices of the code of a program, e.g., of the memory of the
    paused program, see [Bap_emu.project], whose code the program built, so that
    a script follows the values through the code, that runs, without reading its
    disassembly, e.g.,

    {[
      let proj = Emu.project emu in
      (* how the output buffer at out is computed, from the instruction, that
         stores it *)
      let s = Emu.Static.slice proj store [] in
      List.iter s.sites ~f:(printf "%Lx\n");
      (* who reads the slot of .bss, that the instruction at site writes *)
      let s = Emu.Static.slice ~forward:true proj site [ Mem (slot, 8) ] in
      ...
    ]}

    A slice is of the data of one function, the one, whose instruction is at the
    address, over its control flow graph, as BAP lifted it, with the constants
    of its code folded, see [Bap_emu.Xrefs], so that the loads and the stores at
    the addresses, that the code builds, are followed by their bytes, as are the
    slots of the frame, at the offsets from the stack and the frame pointers,
    through their adjustments, e.g., the local variables of the code, that is
    compiled without the optimizations. The loads and the stores at the other
    addresses, e.g., through the pointers, aren't followed through the memory,
    and the slice is incomplete, if their values may come from, or go to, the
    memory, that it follows. The calls are opaque: the callees define the
    registers, that the C ABI of the target returns the results in, and read the
    ones, that it passes the arguments in. *)

open Bap.Std

type location =
  | Reg of string
  | Mem of int64 * int
      (** a register, by the name of the variable of BIR, e.g., [RAX], or of its
          alias, e.g., [X0] for [R0] of AArch64, the case of which doesn't
          matter, or the bytes from an address *)

type slice = {
  sites : int64 list;
      (** the addresses of the instructions, whose values flow to the locations,
          or from them, in their order *)
  live : location list;
      (** the locations, whose values come from before the function, at its
          entry, e.g., its arguments, or go out of it, at its exits, e.g., its
          results, as the registers, and the bytes at the constant addresses *)
  calls : int64 list;
      (** the calls, whose results flow to the locations, or to which their
          values flow, as the arguments *)
  complete : bool;
      (** if no value comes from the memory at the addresses, that aren't known,
          or goes there *)
}

val slice :
  ?forward:bool -> ?addresses:bool -> project -> int64 -> location list -> slice
(** [slice proj addr locations] the backward slice of the values of the
    [locations], as the instruction at [addr] has them before it runs, or, with
    [forward], the forward slice of the values, that the instruction leaves in
    the [locations], over the function, whose instruction it is: the
    instructions, whose values flow to them, or to which their values flow,
    through the registers, the slots of the frame, and the memory at the
    constant addresses, and through the addresses of the loads and the stores,
    if [addresses]. Without the [locations], the slice is of the values, that
    the instruction reads, or, with [forward], writes, e.g., of the stores of
    the instruction, so that the forward slice from a store tells, who reads its
    bytes, also the slots of the frame, which the locations don't name. The
    instruction at [addr] isn't in the slice.

    Raises [Invalid_argument], if no instruction of the program is at [addr]. *)
