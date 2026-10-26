exception Error of int * string

type arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

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

module Cpu = struct
  let arm64_max = 3
  let mips32r6_generic = 14
  let mips64r2_generic = 5
  let mips64_i6400 = 8
end

module Trace = Bap_native_trace

type taint = int

let no_taint = 0
let tainted x = x <> 0

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

type hook = { delete : unit -> unit }
type context = { restore : unit -> unit }

type t = {
  close : unit -> unit;
  set_cpu_model : int -> unit;
  set_tlb_virtual : unit -> unit;
  flush_tb : unit -> unit;
  insn_at :
    int64 -> (string * string * bool * Bap.Std.blk Bap.Std.term list) option;
  insn_addrs : unit -> int64 list;
  inventory : unit -> int * int * int;
  mem_map : int64 -> int64 -> Perm.t -> unit;
  mem_unmap : int64 -> int64 -> unit;
  mem_protect : int64 -> int64 -> Perm.t -> unit;
  mem_write : int64 -> string -> unit;
  mem_read : int64 -> int -> string;
  mem_regions : unit -> (int64 * int64 * Perm.t) list;
  set_unmapped : string -> Bap.Std.word -> unit;
  reg_size : int -> int;
  reg_read : int -> int64;
  reg_write : int -> int64 -> unit;
  current : pc:int -> int64;
  reg_read_bytes : int -> string;
  reg_write_bytes : int -> string -> unit;
  registers_restored : unit -> unit;
  start :
    ?until:int64 -> ?timeout:int -> ?count:int -> ?thread:int -> int64 -> unit;
  stop : unit -> unit;
  in_atomic : unit -> bool;
  taint_start : ?jumps:bool -> unit -> unit;
  taint_stop : unit -> unit;
  taint_active : unit -> bool;
  taint_any : unit -> bool;
  taint_clear : ?regs:bool -> ?mem:bool -> unit -> unit;
  taint_labels : (int * [ `All | `Moves | `None ]) list -> unit;
  reg_labels : string -> int list;
  set_reg_labels : string -> int list -> unit;
  mem_labels : int64 -> int list;
  set_mem_labels : int64 -> int list -> unit;
  tainted_regs : unit -> string list;
  tainted_mem : unit -> int64 list;
  taint_changes : unit -> string list * int64 list;
  taint_jumps : unit -> bool;
  union_taint : taint -> taint -> taint;
  moves_taint : taint -> taint;
  reg_taint : string -> taint;
  mem_range_taint : int64 -> int -> taint;
  set_reg_taint : string -> taint -> unit;
  fill_mem_taint : int64 -> int -> taint -> unit;
  copy_mem_taint : dst:int64 -> src:int64 -> int -> unit;
  move_mem_taint : dst:int64 -> src:int64 -> int -> unit;
  attempt : unit -> int64 option;
  on_code : ?first:int64 -> ?last:int64 -> (int64 -> int -> unit) -> hook;
  on_sites : int64 list -> (int64 -> int -> unit) -> hook list;
  on_block : ?first:int64 -> ?last:int64 -> (int64 -> int -> unit) -> hook;
  on_interrupt : (int -> unit) -> hook;
  on_x86_syscall : (unit -> unit) -> hook list;
  on_invalid_insn : (unit -> bool) -> hook;
  on_unsupported : (int64 -> unit) -> hook;
  on_mem :
    ?first:int64 ->
    ?last:int64 ->
    [ `read | `write | `fetch | `read_after ] list ->
    (access -> int64 -> int -> int64 -> unit) ->
    hook;
  on_mem_invalid :
    ?first:int64 ->
    ?last:int64 ->
    [ `read | `write | `fetch ] list ->
    [ `unmapped | `prot ] list ->
    (access -> int64 -> int -> int64 -> bool) ->
    hook;
  trace :
    ?first:int64 ->
    ?last:int64 ->
    ?watch:int64 * int64 ->
    ?memory:bool ->
    Trace.t ->
    hook list;
  save : unit -> context;
}

type engine = t

let close t = t.close ()
let set_cpu_model t = t.set_cpu_model
let set_tlb_virtual t = t.set_tlb_virtual ()
let flush_tb t = t.flush_tb ()
let insn_at t = t.insn_at
let insn_addrs t = t.insn_addrs ()
let inventory t = t.inventory ()
let mem_map t = t.mem_map
let mem_unmap t = t.mem_unmap
let mem_protect t = t.mem_protect
let mem_write t = t.mem_write
let mem_read t = t.mem_read
let mem_regions t = t.mem_regions ()
let set_unmapped t = t.set_unmapped
let reg_size t = t.reg_size
let reg_read t = t.reg_read
let reg_write t = t.reg_write
let current t ~pc = t.current ~pc
let reg_read_bytes t = t.reg_read_bytes
let reg_write_bytes t = t.reg_write_bytes
let registers_restored t = t.registers_restored ()

let start ?until ?timeout ?count ?thread t =
  t.start ?until ?timeout ?count ?thread

let stop t = t.stop ()
let in_atomic t = t.in_atomic ()
let taint_start ?jumps t = t.taint_start ?jumps ()
let taint_stop t = t.taint_stop ()
let taint_active t = t.taint_active ()
let taint_any t = t.taint_any ()
let taint_clear ?regs ?mem t = t.taint_clear ?regs ?mem ()
let taint_labels t = t.taint_labels
let reg_labels t = t.reg_labels
let set_reg_labels t = t.set_reg_labels
let mem_labels t = t.mem_labels
let set_mem_labels t = t.set_mem_labels
let tainted_regs t = t.tainted_regs ()
let tainted_mem t = t.tainted_mem ()
let taint_changes t = t.taint_changes ()
let taint_jumps t = t.taint_jumps ()
let union_taint t = t.union_taint
let moves_taint t = t.moves_taint
let reg_taint t = t.reg_taint
let mem_range_taint t = t.mem_range_taint
let set_reg_taint t = t.set_reg_taint
let fill_mem_taint t = t.fill_mem_taint
let copy_mem_taint t = t.copy_mem_taint
let move_mem_taint t = t.move_mem_taint
let attempt t = t.attempt ()
let on_code ?first ?last t = t.on_code ?first ?last
let on_sites t = t.on_sites
let on_block ?first ?last t = t.on_block ?first ?last
let on_interrupt t = t.on_interrupt
let on_x86_syscall t = t.on_x86_syscall
let on_invalid_insn t = t.on_invalid_insn
let on_unsupported t = t.on_unsupported
let on_mem ?first ?last t = t.on_mem ?first ?last
let on_mem_invalid ?first ?last t = t.on_mem_invalid ?first ?last
let delete h = h.delete ()
let trace ?first ?last ?watch ?memory t = t.trace ?first ?last ?watch ?memory
let save t = t.save ()
let restore c = c.restore ()

module type S = sig
  type t
  type hook
  type context

  val close : t -> unit
  val set_cpu_model : t -> int -> unit
  val set_tlb_virtual : t -> unit
  val flush_tb : t -> unit

  val insn_at :
    t ->
    int64 ->
    (string * string * bool * Bap.Std.blk Bap.Std.term list) option

  val insn_addrs : t -> int64 list
  val inventory : t -> int * int * int
  val mem_map : t -> int64 -> int64 -> Perm.t -> unit
  val mem_unmap : t -> int64 -> int64 -> unit
  val mem_protect : t -> int64 -> int64 -> Perm.t -> unit
  val mem_write : t -> int64 -> string -> unit
  val mem_read : t -> int64 -> int -> string
  val mem_regions : t -> (int64 * int64 * Perm.t) list
  val set_unmapped : t -> string -> Bap.Std.word -> unit
  val reg_size : t -> int -> int
  val reg_read : t -> int -> int64
  val reg_write : t -> int -> int64 -> unit
  val current : t -> pc:int -> int64
  val reg_read_bytes : t -> int -> string
  val reg_write_bytes : t -> int -> string -> unit
  val registers_restored : t -> unit

  val start :
    ?until:int64 ->
    ?timeout:int ->
    ?count:int ->
    ?thread:int ->
    t ->
    int64 ->
    unit

  val stop : t -> unit
  val in_atomic : t -> bool
  val taint_start : ?jumps:bool -> t -> unit
  val taint_stop : t -> unit
  val taint_active : t -> bool
  val taint_any : t -> bool
  val taint_clear : ?regs:bool -> ?mem:bool -> t -> unit
  val taint_labels : t -> (int * [ `All | `Moves | `None ]) list -> unit
  val reg_labels : t -> string -> int list
  val set_reg_labels : t -> string -> int list -> unit
  val mem_labels : t -> int64 -> int list
  val set_mem_labels : t -> int64 -> int list -> unit
  val tainted_regs : t -> string list
  val tainted_mem : t -> int64 list
  val taint_changes : t -> string list * int64 list
  val no_taint : taint
  val tainted : taint -> bool
  val taint_jumps : t -> bool
  val union_taint : t -> taint -> taint -> taint
  val moves_taint : t -> taint -> taint
  val reg_taint : t -> string -> taint
  val mem_range_taint : t -> int64 -> int -> taint
  val set_reg_taint : t -> string -> taint -> unit
  val fill_mem_taint : t -> int64 -> int -> taint -> unit
  val copy_mem_taint : t -> dst:int64 -> src:int64 -> int -> unit
  val move_mem_taint : t -> dst:int64 -> src:int64 -> int -> unit
  val attempt : t -> int64 option

  val on_code :
    ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

  val on_sites : t -> int64 list -> (int64 -> int -> unit) -> hook list

  val on_block :
    ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

  val on_interrupt : t -> (int -> unit) -> hook
  val on_x86_syscall : t -> (unit -> unit) -> hook list
  val on_invalid_insn : t -> (unit -> bool) -> hook
  val on_unsupported : t -> (int64 -> unit) -> hook

  val on_mem :
    ?first:int64 ->
    ?last:int64 ->
    t ->
    [ `read | `write | `fetch | `read_after ] list ->
    (access -> int64 -> int -> int64 -> unit) ->
    hook

  val on_mem_invalid :
    ?first:int64 ->
    ?last:int64 ->
    t ->
    [ `read | `write | `fetch ] list ->
    [ `unmapped | `prot ] list ->
    (access -> int64 -> int -> int64 -> bool) ->
    hook

  val delete : hook -> unit

  val trace :
    ?first:int64 ->
    ?last:int64 ->
    ?watch:int64 * int64 ->
    ?memory:bool ->
    t ->
    Trace.t ->
    hook list

  val save : t -> context
  val restore : context -> unit
end

module type BACKEND = S

module Make (B : BACKEND) = struct
  include B

  let erase t =
    let hook h = { delete = (fun () -> B.delete h) } in
    {
      close = (fun () -> B.close t);
      set_cpu_model = B.set_cpu_model t;
      set_tlb_virtual = (fun () -> B.set_tlb_virtual t);
      flush_tb = (fun () -> B.flush_tb t);
      insn_at = B.insn_at t;
      insn_addrs = (fun () -> B.insn_addrs t);
      inventory = (fun () -> B.inventory t);
      mem_map = B.mem_map t;
      mem_unmap = B.mem_unmap t;
      mem_protect = B.mem_protect t;
      mem_write = B.mem_write t;
      mem_read = B.mem_read t;
      mem_regions = (fun () -> B.mem_regions t);
      set_unmapped = B.set_unmapped t;
      reg_size = B.reg_size t;
      reg_read = B.reg_read t;
      reg_write = B.reg_write t;
      current = (fun ~pc -> B.current t ~pc);
      reg_read_bytes = B.reg_read_bytes t;
      reg_write_bytes = B.reg_write_bytes t;
      registers_restored = (fun () -> B.registers_restored t);
      start =
        (fun ?until ?timeout ?count ?thread pc ->
          B.start ?until ?timeout ?count ?thread t pc);
      stop = (fun () -> B.stop t);
      in_atomic = (fun () -> B.in_atomic t);
      taint_start = (fun ?jumps () -> B.taint_start ?jumps t);
      taint_stop = (fun () -> B.taint_stop t);
      taint_active = (fun () -> B.taint_active t);
      taint_any = (fun () -> B.taint_any t);
      taint_clear = (fun ?regs ?mem () -> B.taint_clear ?regs ?mem t);
      taint_labels = B.taint_labels t;
      reg_labels = B.reg_labels t;
      set_reg_labels = B.set_reg_labels t;
      mem_labels = B.mem_labels t;
      set_mem_labels = B.set_mem_labels t;
      tainted_regs = (fun () -> B.tainted_regs t);
      tainted_mem = (fun () -> B.tainted_mem t);
      taint_changes = (fun () -> B.taint_changes t);
      taint_jumps = (fun () -> B.taint_jumps t);
      union_taint = B.union_taint t;
      moves_taint = B.moves_taint t;
      reg_taint = B.reg_taint t;
      mem_range_taint = B.mem_range_taint t;
      set_reg_taint = B.set_reg_taint t;
      fill_mem_taint = B.fill_mem_taint t;
      copy_mem_taint = B.copy_mem_taint t;
      move_mem_taint = B.move_mem_taint t;
      attempt = (fun () -> B.attempt t);
      on_code = (fun ?first ?last f -> hook (B.on_code ?first ?last t f));
      on_sites = (fun sites f -> List.map hook (B.on_sites t sites f));
      on_block = (fun ?first ?last f -> hook (B.on_block ?first ?last t f));
      on_interrupt = (fun f -> hook (B.on_interrupt t f));
      on_x86_syscall = (fun f -> List.map hook (B.on_x86_syscall t f));
      on_invalid_insn = (fun f -> hook (B.on_invalid_insn t f));
      on_unsupported = (fun f -> hook (B.on_unsupported t f));
      on_mem =
        (fun ?first ?last accesses f ->
          hook (B.on_mem ?first ?last t accesses f));
      on_mem_invalid =
        (fun ?first ?last accesses kinds f ->
          hook (B.on_mem_invalid ?first ?last t accesses kinds f));
      trace =
        (fun ?first ?last ?watch ?memory trace ->
          List.map hook (B.trace ?first ?last ?watch ?memory t trace));
      save =
        (fun () ->
          let c = B.save t in
          { restore = (fun () -> B.restore c) });
    }
end
