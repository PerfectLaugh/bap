(** A static linker for relocatable ELF files.

    A relocatable file (an object file or a kernel module) has no memory layout
    and its code and data are incomplete until the relocations are applied. The
    linker assigns addresses to the allocatable sections, allocates the storage
    for the common and external (undefined) symbols as well as for the global
    offset table, and applies the relocations, like a real static linker would
    do (and as Ghidra's ELF loader does).

    The linker doesn't modify the input, it computes the list of patches that
    should be applied to it. The patches could lie past the end of the input,
    the extension holds the synthesized global offset table. *)

open Core

type section = {
  index : int;
  name : string;
  typ : int;  (** sh_type *)
  flags : int64;  (** sh_flags *)
  off : int64;
  size : int64;
  align : int64;
}

type symbol = {
  name : string;
  shndx : int;
      (** st_shndx, or the extended section index if st_shndx is SHN_XINDEX *)
  extended : bool;
      (** [true] if [shndx] is an extended section index, which is never one of
          the special indices (e.g., SHN_ABS) *)
  value : int64;
  size : int64;
  typ : int;  (** the symbol type, e.g., STT_FUNC *)
  bind : int;  (** the symbol binding, e.g., STB_LOCAL *)
}

type relocation = {
  section : int;  (** the index of the relocated section *)
  offset : int64;  (** r_offset *)
  typ : int;  (** the machine specific type of the relocation *)
  symbol : int;  (** the index of the symbol *)
  addend : int64;  (** r_addend, if [explicit] *)
  explicit : bool;  (** [true] if the addend is explicit (RELA) *)
}

type input = {
  machine : int;  (** e_machine *)
  width : int;  (** the address size in bits *)
  little : bool;  (** [true] if the data is little endian *)
  base : int64;  (** the address of the first section *)
  data : Bigstring.t;  (** the contents of the file *)
  sections : section list;
  symbols : symbol Int.Map.t;  (** symbols by their indices *)
  relocations : relocation list;  (** in the order of appearance *)
}

type region = {
  name : string;
  addr : int64;
  size : int64;
  off : int64 option;
      (** the offset of the region contents, if they are present *)
  r : bool;
  w : bool;
  x : bool;
  is_section : bool;  (** [false] for regions synthesized by the linker *)
}

type output = {
  regions : region list;
  functions : (string * int64 * int64 * int64) list;
      (** [(name, addr, size, value)], where [value] is the address with the
          machine specific bits, e.g., the Thumb bit *)
  references : (int64 * string) list;
      (** [(fixup, name)] the relocated place references an external symbol *)
  patches : (int64 * string) list;
      (** [(off, bytes)] the [bytes] should be stored at the offset [off]. The
          patches are ordered by their offsets and don't intersect, a patch may
          contain unmodified bytes between the modified ones. *)
  warnings : string list;
}

val link : input -> output
