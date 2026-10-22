exception Error of int * string

let () = Callback.register_exception "Bap_unicorn.Error" (Error (0, ""))

type t
type arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

(* the values of uc_arch *)
let arch_code = function
  | Arm -> 1
  | Arm64 -> 2
  | Mips -> 3
  | X86 -> 4
  | Ppc -> 5
  | Riscv -> 8

module Mode = struct
  type t = int

  let ( + ) = ( lor )
  let little_endian = 0
  let big_endian = 1 lsl 30
  let arm = 0
  let thumb = 1 lsl 4
  let mclass = 1 lsl 5
  let v8 = 1 lsl 6
  let mips32 = 1 lsl 2
  let mips64 = 1 lsl 3
  let mode16 = 1 lsl 1
  let mode32 = 1 lsl 2
  let mode64 = 1 lsl 3
  let ppc32 = 1 lsl 2
  let ppc64 = 1 lsl 3
  let riscv32 = 1 lsl 2
  let riscv64 = 1 lsl 3
end

module Perm = struct
  type t = int

  let ( + ) = ( lor )
  let ( - ) x y = x land lnot y
  let none = 0
  let read = 1
  let write = 2
  let exec = 4
  let all = 7
  let mem perms perm = perms land perm = perm
end

external version : unit -> int * int = "bap_uc_version"
external supported_code : int -> bool = "bap_uc_arch_supported"
external create_code : int -> Mode.t -> t = "bap_uc_open"
external close : t -> unit = "bap_uc_close"
external set_cpu_model : t -> int -> unit = "bap_uc_set_cpu_model"
external flush_tb : t -> unit = "bap_uc_flush_tb"
external set_tlb_virtual : t -> unit = "bap_uc_set_tlb_virtual"
external mem_map : t -> int64 -> int64 -> Perm.t -> unit = "bap_uc_mem_map"
external mem_unmap : t -> int64 -> int64 -> unit = "bap_uc_mem_unmap"

external mem_protect : t -> int64 -> int64 -> Perm.t -> unit
  = "bap_uc_mem_protect"

external mem_write : t -> int64 -> string -> unit = "bap_uc_mem_write"
external mem_read : t -> int64 -> int -> string = "bap_uc_mem_read"
external mem_regions : t -> (int64 * int64 * Perm.t) list = "bap_uc_mem_regions"
external regs_code : int -> (string * int) list = "bap_uc_regs"
external reg_size : t -> int -> int = "bap_uc_reg_size"
external reg_read : t -> int -> int64 = "bap_uc_reg_read"
external reg_write : t -> int -> int64 -> unit = "bap_uc_reg_write"
external reg_read_bytes : t -> int -> string = "bap_uc_reg_read_bytes"
external reg_write_bytes : t -> int -> string -> unit = "bap_uc_reg_write_bytes"

external emu_start : t -> int64 -> int64 -> int64 -> int -> unit
  = "bap_uc_emu_start"

external stop : t -> unit = "bap_uc_emu_stop"
external hook_del : t -> int64 -> unit = "bap_uc_hook_del"

let supported arch = supported_code (arch_code arch)
let create arch mode = create_code (arch_code arch) mode
let regs arch = regs_code (arch_code arch)

let reg arch name =
  let name = String.uppercase_ascii name in
  List.assoc_opt name (regs arch)

(* Unicorn stops at [until], which is never reached by default, as the
   program counter, even of 64 bits, is never all ones *)
let start ?(until = -1L) ?(timeout = 0) ?(count = 0) uc pc =
  emu_start uc pc until (Int64.of_int timeout) count

type hook = int64

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

(* the kinds of the hooks in unicorn_stubs.c *)
type kind = Code | Block | Intr | Insn_invalid | Mem | Mem_event | Insn

external hook_add : t -> kind -> int -> int64 -> int64 -> 'f -> int64
  = "bap_uc_hook_add_bytecode" "bap_uc_hook_add"

(* the first address after the last one means all addresses *)
let hook ?(first = 1L) ?(last = 0L) uc kind types f =
  hook_add uc kind types first last f

let on_code ?first ?last uc (f : int64 -> int -> unit) =
  hook ?first ?last uc Code 0 f

let on_block ?first ?last uc (f : int64 -> int -> unit) =
  hook ?first ?last uc Block 0 f

let on_interrupt uc (f : int -> unit) = hook uc Intr 0 f

external x86_syscalls : unit -> int * int = "bap_uc_x86_syscalls"

let on_x86_syscall uc (f : unit -> unit) =
  let syscall, sysenter = x86_syscalls () in
  [ hook uc Insn syscall f; hook uc Insn sysenter f ]

let on_invalid_insn uc (f : unit -> bool) = hook uc Insn_invalid 0 f

(* the values of uc_hook_type *)
let mask = List.fold_left (fun m x -> m lor x) 0

let on_mem ?first ?last uc accesses
    (f : access -> int64 -> int -> int64 -> unit) =
  let types =
    mask
    @@ List.map
         (function
           | `read -> 1 lsl 10
           | `write -> 1 lsl 11
           | `fetch -> 1 lsl 12
           | `read_after -> 1 lsl 13)
         accesses
  in
  hook ?first ?last uc Mem types f

let on_mem_invalid ?first ?last uc accesses kinds
    (f : access -> int64 -> int -> int64 -> bool) =
  let types =
    mask
    @@ List.concat_map
         (fun kind ->
           List.map
             (fun access ->
               match (kind, access) with
               | `unmapped, `read -> 1 lsl 4
               | `unmapped, `write -> 1 lsl 5
               | `unmapped, `fetch -> 1 lsl 6
               | `prot, `read -> 1 lsl 7
               | `prot, `write -> 1 lsl 8
               | `prot, `fetch -> 1 lsl 9)
             accesses)
         kinds
  in
  hook ?first ?last uc Mem_event types f

let delete = hook_del

module Trace = struct
  type t
  type pcs = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  type sizes = (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

  type accesses =
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array2.t

  external create : int -> int -> bool -> int -> t = "bap_uc_trace_create"
  external count : t -> int64 = "bap_uc_trace_count"
  external accesses_count : t -> int64 = "bap_uc_trace_accesses_count"
  external clear : t -> unit = "bap_uc_trace_clear"
  external blocks : t -> bool = "bap_uc_trace_blocks"
  external pcs : t -> int -> pcs = "bap_uc_trace_pcs"
  external sizes : t -> int -> sizes = "bap_uc_trace_sizes"
  external accesses : t -> int -> accesses = "bap_uc_trace_mem"
  external save : t -> int -> string -> int64 = "bap_uc_trace_save"
  external bounds : t -> pcs = "bap_uc_trace_bounds"

  let create ?(every = 1) ?(blocks = false) ?(accesses = 0) size =
    create size every blocks accesses

  let pcs ?(last = -1) t = pcs t last
  let sizes ?(last = -1) t = sizes t last
  let accesses ?(last = -1) t = accesses t last
  let save ?(last = -1) t file = save t last file
end

(* the kinds of the native hooks in unicorn_stubs.c *)
type trace_kind = Trace_code | Trace_block | Trace_mem

external trace_add : t -> Trace.t -> trace_kind -> int64 -> int64 -> int64
  = "bap_uc_trace_add"

let trace ?(first = 1L) ?(last = 0L) ?(memory = false) uc trace =
  let kind = if Trace.blocks trace then Trace_block else Trace_code in
  let code = trace_add uc trace kind first last in
  if memory then [ code; trace_add uc trace Trace_mem 1L 0L ] else [ code ]

type context

external save : t -> context = "bap_uc_context_save"
external restore : t -> context -> unit = "bap_uc_context_restore"
