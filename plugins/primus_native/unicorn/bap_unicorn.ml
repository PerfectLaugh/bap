exception Error = Bap_engine.Error

let () = Callback.register_exception "Bap_unicorn.Error" (Error (0, ""))

type t
type arch = Bap_engine.arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

module Mode = Bap_engine.Mode
module Perm = Bap_engine.Perm

(* the values of uc_arch *)
let arch_code = function
  | Arm -> 1
  | Arm64 -> 2
  | Mips -> 3
  | X86 -> 4
  | Ppc -> 5
  | Riscv -> 8

external version : unit -> int * int = "bap_uc_version"
external supported_code : int -> bool = "bap_uc_arch_supported"
external create_code : int -> Mode.t -> t = "bap_uc_open"
external close : t -> unit = "bap_uc_close"

module Cpu = Bap_engine.Cpu

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
external registers_restored : t -> unit = "bap_uc_registers_restored"

external emu_start : t -> int64 -> int64 -> int64 -> int -> int -> unit
  = "bap_uc_emu_start_bytecode" "bap_uc_emu_start"

external stop : t -> unit = "bap_uc_emu_stop"
external interrupted : unit -> bool = "bap_uc_interrupted"
external process_signals : unit -> unit = "bap_uc_process_signals"
external hook_del : t -> int64 -> unit = "bap_uc_hook_del"
external attempt : t -> int64 = "bap_uc_attempt"

let supported arch = supported_code (arch_code arch)
let create arch mode = create_code (arch_code arch) mode

(* the registers of the architectures, whose table the stubs build, are
   cached, as the executor looks them up, while it runs *)
let tables = Hashtbl.create 8

let table arch =
  match Hashtbl.find_opt tables arch with
  | Some table -> table
  | None ->
      let regs = regs_code (arch_code arch) in
      let table = Hashtbl.create (List.length regs) in
      (* the first of the same names, as [List.assoc] finds it *)
      List.iter
        (fun (name, id) ->
          if not (Hashtbl.mem table name) then Hashtbl.add table name id)
        regs;
      Hashtbl.replace tables arch (regs, table);
      (regs, table)

let regs arch = fst (table arch)

let reg arch name =
  Hashtbl.find_opt (snd (table arch)) (String.uppercase_ascii name)

(* Unicorn stops at [until], which is never reached by default, as the
   program counter, even of 64 bits, is never all ones *)
let start ?(until = -1L) ?(timeout = 0) ?(count = 0) ?(thread = 0) uc pc =
  emu_start uc pc until (Int64.of_int timeout) count thread

type hook = int64

type access = Bap_engine.access =
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

external hook_sites : t -> int64 array -> 'f -> int64 = "bap_uc_hook_sites"

(* the sites go to the hooks of their clusters, whose ranges are from
   their first sites to their last ones, which are at most [gap] bytes
   apart, and which find the sites natively, as Unicorn calls a hook at
   each instruction of its range, so that a range spans few instructions,
   that aren't sites, e.g., of a loop, that runs between two sites *)
let on_sites uc sites (f : int64 -> int -> unit) =
  let gap = 16L in
  List.sort_uniq Int64.unsigned_compare sites
  |> List.fold_left
       (fun clusters x ->
         match clusters with
         | (y :: _ as cluster) :: rest
           when Int64.unsigned_compare (Int64.sub x y) gap <= 0 ->
             (x :: cluster) :: rest
         | _ -> [ x ] :: clusters)
       []
  |> List.rev_map (fun cluster ->
      hook_sites uc (Array.of_list (List.rev cluster)) f)

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

module Trace = Bap_native_trace

(* the kinds of the native hooks in unicorn_stubs.c *)
type trace_kind = Trace_code | Trace_block | Trace_mem | Trace_mode

external trace_add : t -> Trace.t -> trace_kind -> int64 -> int64 -> int64
  = "bap_uc_trace_add"

(* the trace of the code of ARM has the modes of its blocks, whose hook
   isn't there on the other targets *)
let trace ?(first = 1L) ?(last = 0L) ?watch ?(memory = false) uc trace =
  let kind = if Trace.blocks trace then Trace_block else Trace_code in
  let mode = trace_add uc trace Trace_mode 1L 0L in
  let code = trace_add uc trace kind first last in
  (* the hooks of the memory of Unicorn are of the addresses, that the
     accesses start at *)
  let lower, upper = Option.value watch ~default:(1L, 0L) in
  List.filter (( <> ) (-1L))
    ([ mode; code ]
    @ if memory then [ trace_add uc trace Trace_mem lower upper ] else [])

type context

external save : t -> context = "bap_uc_context_save"
external restore : t -> context -> unit = "bap_uc_context_restore"
