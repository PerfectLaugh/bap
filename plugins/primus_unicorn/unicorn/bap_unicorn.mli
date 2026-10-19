(** The bindings to the Unicorn emulator engine.

    A thin layer over the C API of Unicorn, which raises [Error] when a function
    of Unicorn fails. The addresses and the values are unsigned 64-bit integers,
    represented with [int64].

    The hooks hold their closures until they are deleted or the engine is
    closed. A closure that captures the engine keeps it alive, so the engines
    with such hooks should be closed explicitly. *)

exception Error of int * string
(** [Error (code, message)] is the error of Unicorn with its code. *)

type t
(** an instance of the emulator *)

type arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

val version : unit -> int * int
(** the major and minor versions of the library *)

val supported : arch -> bool
(** [supported arch] if the engine of [arch] is linked. *)

module Mode : sig
  type t = private int

  val ( + ) : t -> t -> t
  val little_endian : t
  val big_endian : t
  val arm : t
  val thumb : t
  val mclass : t
  val v8 : t
  val mips32 : t
  val mips64 : t
  val mode16 : t
  val mode32 : t
  val mode64 : t
  val ppc32 : t
  val ppc64 : t
  val riscv32 : t
  val riscv64 : t
end

module Perm : sig
  type t = private int

  val ( + ) : t -> t -> t
  val none : t
  val read : t
  val write : t
  val exec : t
  val all : t
  val mem : t -> t -> bool
end

val create : arch -> Mode.t -> t
(** [create arch mode] opens the emulator. *)

val close : t -> unit
(** [close uc] releases the emulator and its hooks. Using a closed emulator
    raises [Invalid_argument]. Closing it again does nothing. *)

val set_cpu_model : t -> int -> unit
(** [set_cpu_model uc model] selects the CPU, one of the UC_CPU_* constants of
    the architecture. It must be done before the first other operation. *)

val set_tlb_virtual : t -> unit
(** [set_tlb_virtual uc] maps the virtual addresses to the same physical
    addresses, bypassing the MMU of the CPU, e.g., the TLB of MIPS. It must be
    done before the first other operation. *)

val flush_tb : t -> unit
(** [flush_tb uc] drops the translated code. *)

(** {2 Memory} *)

val mem_map : t -> int64 -> int64 -> Perm.t -> unit
(** [mem_map uc addr size perm] maps the region, both [addr] and [size] are
    aligned to 4 KB. *)

val mem_unmap : t -> int64 -> int64 -> unit
val mem_protect : t -> int64 -> int64 -> Perm.t -> unit
val mem_write : t -> int64 -> string -> unit
val mem_read : t -> int64 -> int -> string

val mem_regions : t -> (int64 * int64 * Perm.t) list
(** the mapped regions, with their first and last addresses *)

(** {2 Registers} *)

val regs : arch -> (string * int) list
(** [regs arch] the names of the registers of [arch], as in the headers of
    Unicorn without the prefix, e.g., ["RAX"] for UC_X86_REG_RAX, and their
    identifiers. Some identifiers have several names. *)

val reg : arch -> string -> int option
(** [reg arch name] the identifier of the register of [arch], the case of [name]
    does not matter. *)

val reg_size : t -> int -> int
(** the size of the register in bytes *)

val reg_read : t -> int -> int64
(** [reg_read uc reg] the value of the register, which is at most 8 bytes wide,
    zero-extended. *)

val reg_write : t -> int -> int64 -> unit
(** [reg_write uc reg x] writes [x], truncated to the size of the register,
    which is at most 8 bytes wide. *)

val reg_read_bytes : t -> int -> string
(** [reg_read_bytes uc reg] the bytes of the register, of any size, in the order
    of the host. *)

val reg_write_bytes : t -> int -> string -> unit
(** [reg_write_bytes uc reg bytes] writes the bytes, which have the size of the
    register. *)

(** {2 Emulation} *)

val start : ?until:int64 -> ?timeout:int -> ?count:int -> t -> int64 -> unit
(** [start uc pc] runs the code from [pc] until it reaches [until], runs out of
    [timeout] microseconds, executes [count] instructions, or {!stop} is called.
    Reraises the exception of a hook, which stops the emulation. By default,
    there are no limits. *)

val stop : t -> unit
(** [stop uc] stops the emulation, e.g., from a hook. *)

(** {2 Hooks}

    A hook may be called for the addresses from [first] to [last], inclusive, by
    default for all of them. *)

type hook

type access =
  | Read
  | Write
  | Fetch
  | Read_unmapped
  | Write_unmapped
  | Fetch_unmapped
  | Write_prot
  | Read_prot
  | Fetch_prot
  | Read_after

val on_code : ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook
(** [on_code uc f] calls [f addr size] before each instruction. *)

val on_block :
  ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook
(** [on_block uc f] calls [f addr size] before each basic block. *)

val on_interrupt : t -> (int -> unit) -> hook
(** [on_interrupt uc f] calls [f intno] on interrupts and system calls. *)

val on_x86_syscall : t -> (unit -> unit) -> hook list
(** [on_x86_syscall uc f] calls [f ()] on the syscall and sysenter instructions
    of x86, which are not interrupts. *)

val on_invalid_insn : t -> (unit -> bool) -> hook
(** [on_invalid_insn uc f] calls [f ()] on an invalid instruction, the emulation
    continues if it returns [true]. *)

val on_mem :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  [ `read | `write | `fetch | `read_after ] list ->
  (access -> int64 -> int -> int64 -> unit) ->
  hook
(** [on_mem uc accesses f] calls [f access addr size value] on the accesses to
    the mapped memory, [value] is the written value. *)

val on_mem_invalid :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  [ `read | `write | `fetch ] list ->
  [ `unmapped | `prot ] list ->
  (access -> int64 -> int -> int64 -> bool) ->
  hook
(** [on_mem_invalid uc accesses kinds f] calls [f access addr size value] on the
    invalid accesses, the emulation continues if [f] returns [true], e.g., after
    it has mapped the memory. *)

val delete : t -> hook -> unit
(** [delete uc hook] removes the hook. *)

(** {2 Contexts} *)

type context
(** the saved values of the registers *)

val save : t -> context
val restore : t -> context -> unit
