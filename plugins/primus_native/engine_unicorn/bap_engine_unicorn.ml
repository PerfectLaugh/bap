include Bap_engine
module Uc = Bap_unicorn

module Direct = struct
  type t = Uc.t
  type hook = (Uc.t * Uc.hook) option
  type context = Uc.t * Uc.context

  let version = Uc.version
  let supported = Uc.supported
  let regs = Uc.regs
  let reg = Uc.reg
  let create = Uc.create
  let close = Uc.close
  let set_cpu_model = Uc.set_cpu_model
  let set_tlb_virtual = Uc.set_tlb_virtual
  let flush_tb = Uc.flush_tb
  let insn_at _ _ = None
  let insn_addrs _ = []
  let inventory _ = (0, 0, 0)
  let mem_map = Uc.mem_map
  let mem_unmap = Uc.mem_unmap
  let mem_protect = Uc.mem_protect
  let mem_write = Uc.mem_write
  let mem_read = Uc.mem_read
  let mem_regions = Uc.mem_regions
  let set_unmapped _ _ _ = ()
  let reg_size = Uc.reg_size
  let reg_read = Uc.reg_read
  let reg_write = Uc.reg_write
  let current t ~pc = Uc.reg_read t pc
  let reg_read_bytes = Uc.reg_read_bytes
  let reg_write_bytes = Uc.reg_write_bytes
  let registers_restored = Uc.registers_restored
  let start = Uc.start
  let stop = Uc.stop
  let in_atomic _ = false
  let taint_start ?jumps:_ _ = invalid_arg "Unicorn doesn't propagate the taint"
  let taint_stop _ = ()
  let taint_active _ = false
  let taint_any _ = false
  let taint_clear ?regs:_ ?mem:_ _ = ()
  let taint_labels _ _ = ()
  let reg_labels _ _ = []
  let set_reg_labels _ _ _ = ()
  let mem_labels _ _ = []
  let set_mem_labels _ _ _ = ()
  let tainted_regs _ = []
  let tainted_mem _ = []
  let taint_changes _ = ([], [])
  let no_taint = Bap_engine.no_taint
  let tainted = Bap_engine.tainted
  let taint_jumps _ = false
  let union_taint _ _ _ = no_taint
  let moves_taint _ _ = no_taint
  let reg_taint _ _ = no_taint
  let mem_range_taint _ _ _ = no_taint
  let set_reg_taint _ _ _ = ()
  let fill_mem_taint _ _ _ _ = ()
  let copy_mem_taint _ ~dst:_ ~src:_ _ = ()
  let move_mem_taint _ ~dst:_ ~src:_ _ = ()
  let interrupted = Uc.interrupted
  let process_signals = Uc.process_signals
  let attempt t = Some (Uc.attempt t)
  let hook t h = Some (t, h)
  let on_code ?first ?last t f = hook t (Uc.on_code ?first ?last t f)
  let on_sites t sites f = List.map (fun h -> hook t h) (Uc.on_sites t sites f)
  let on_block ?first ?last t f = hook t (Uc.on_block ?first ?last t f)
  let on_interrupt t f = hook t (Uc.on_interrupt t f)
  let on_x86_syscall t f = List.map (fun h -> hook t h) (Uc.on_x86_syscall t f)
  let on_invalid_insn t f = hook t (Uc.on_invalid_insn t f)
  let on_unsupported _ _ = None

  let on_mem ?first ?last t accesses f =
    hook t (Uc.on_mem ?first ?last t accesses f)

  let on_mem_invalid ?first ?last t accesses kinds f =
    hook t (Uc.on_mem_invalid ?first ?last t accesses kinds f)

  let delete = function None -> () | Some (t, h) -> Uc.delete t h

  let trace ?first ?last ?watch ?memory t trace =
    List.map (fun h -> hook t h) (Uc.trace ?first ?last ?watch ?memory t trace)

  let save t = (t, Uc.save t)
  let restore (t, c) = Uc.restore t c
end

module _ :
  Bap_engine.S
    with type t = Direct.t
     and type hook = Direct.hook
     and type context = Direct.context =
  Direct

module Erased = Bap_engine.Make (Direct)

let create arch mode = Erased.erase (Direct.create arch mode)
let version = Uc.version
let supported = Uc.supported
let regs = Uc.regs
let reg = Uc.reg
let interrupted = Uc.interrupted
let process_signals = Uc.process_signals
