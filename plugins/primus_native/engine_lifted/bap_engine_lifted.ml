include Bap_engine
module L = Bap_lifted

type config = Bap_lifted.config = {
  lift :
    thumb:bool ->
    int64 ->
    string ->
    (int * string * Bap.Std.blk Bap.Std.term list) option;
  name : Bap.Std.tid -> string option;
  policy : int;
  delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
  locate : string -> (int * int * int) option;
  owner : string -> string option;
  pc : int;
  big_endian : bool;
  bits : int;
  jit : bool;
  cache : string option;
}

module Direct = struct
  type t = L.t
  type hook = L.t * L.hook
  type context = L.t * L.context

  let create = L.create
  let close = L.close
  let set_cpu_model _ _ = ()
  let set_tlb_virtual _ = ()
  let flush_tb = L.flush_tb
  let insn_at = L.insn_at
  let insn_addrs = L.insn_addrs
  let inventory = L.inventory
  let mem_map = L.mem_map
  let mem_unmap = L.mem_unmap
  let mem_protect = L.mem_protect
  let mem_write = L.mem_write
  let mem_read = L.mem_read
  let mem_regions = L.mem_regions
  let set_unmapped = L.set_unmapped
  let reg_size = L.reg_size
  let reg_read = L.reg_read
  let reg_write = L.reg_write
  let current t ~pc:_ = L.current t
  let reg_read_bytes = L.reg_read_bytes
  let reg_write_bytes = L.reg_write_bytes
  let registers_restored = L.registers_restored
  let start = L.start
  let stop = L.stop
  let in_atomic = L.in_atomic
  let taint_start = L.taint_start
  let taint_stop = L.taint_stop
  let taint_active = L.taint_active
  let taint_any = L.taint_any
  let taint_clear = L.taint_clear
  let taint_labels = L.taint_labels
  let reg_labels = L.reg_labels
  let set_reg_labels = L.set_reg_labels
  let mem_labels = L.mem_labels
  let set_mem_labels = L.set_mem_labels
  let tainted_regs = L.tainted_regs
  let tainted_mem = L.tainted_mem
  let taint_changes = L.taint_changes
  let no_taint = Bap_engine.no_taint
  let tainted = Bap_engine.tainted
  let taint_jumps = L.taint_jumps
  let union_taint = L.union_taint
  let moves_taint = L.moves_taint
  let reg_taint = L.reg_taint
  let mem_range_taint = L.mem_range_taint
  let set_reg_taint = L.set_reg_taint
  let fill_mem_taint = L.fill_mem_taint
  let copy_mem_taint = L.copy_mem_taint
  let move_mem_taint = L.move_mem_taint
  let attempt _ = None
  let hook t h = (t, h)
  let on_code ?first ?last t f = hook t (L.on_code ?first ?last t f)
  let on_sites t sites f = [ hook t (L.on_sites t sites f) ]
  let on_block ?first ?last t f = hook t (L.on_block ?first ?last t f)
  let on_interrupt t f = hook t (L.on_interrupt t f)
  let on_x86_syscall _ _ = []
  let on_invalid_insn t f = hook t (L.on_invalid_insn t f)
  let on_unsupported t f = hook t (L.on_unsupported t f)

  let on_mem ?first ?last t accesses f =
    hook t (L.on_mem ?first ?last t accesses f)

  let on_mem_invalid ?first ?last t accesses kinds f =
    hook t (L.on_mem_invalid ?first ?last t accesses kinds f)

  let delete (t, h) = L.delete t h

  let trace ?first ?last ?watch ?memory t trace =
    List.map (fun h -> hook t h) (L.trace ?first ?last ?watch ?memory t trace)

  let save t = (t, L.save t)
  let restore (t, c) = L.restore t c
end

module _ :
  Bap_engine.S
    with type t = Direct.t
     and type hook = Direct.hook
     and type context = Direct.context =
  Direct

module Erased = Bap_engine.Make (Direct)

let create config arch mode = Erased.erase (Direct.create config arch mode)
