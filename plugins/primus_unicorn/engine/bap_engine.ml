module Uc = Bap_unicorn
module L = Bap_engine_lifted

exception Error = Bap_unicorn.Error

type t = Unicorn of Uc.t | Lifted of L.t
type arch = Bap_unicorn.arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

module Mode = Bap_unicorn.Mode
module Perm = Bap_unicorn.Perm
module Cpu = Bap_unicorn.Cpu

module Lifted = struct
  type config = L.config = {
    lift :
      thumb:bool ->
      int64 ->
      string ->
      (int * string * Bap.Std.blk Bap.Std.term list) option;
    name : Bap.Std.tid -> string option;
    policy : int;
    delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
    locate : string -> (int * int * int) option;
    pc : int;
    big_endian : bool;
    bits : int;
  }
end

let version = Uc.version
let supported = Uc.supported
let create arch mode = Unicorn (Uc.create arch mode)
let create_lifted config arch mode = Lifted (L.create config arch mode)
let is_lifted = function Unicorn _ -> false | Lifted _ -> true
let close = function Unicorn u -> Uc.close u | Lifted l -> L.close l

let set_cpu_model t model =
  match t with Unicorn u -> Uc.set_cpu_model u model | Lifted _ -> ()

let set_tlb_virtual = function
  | Unicorn u -> Uc.set_tlb_virtual u
  | Lifted _ -> ()

let flush_tb = function Unicorn u -> Uc.flush_tb u | Lifted l -> L.flush_tb l

let mem_map t addr size perm =
  match t with
  | Unicorn u -> Uc.mem_map u addr size perm
  | Lifted l -> L.mem_map l addr size perm

let mem_unmap t addr size =
  match t with
  | Unicorn u -> Uc.mem_unmap u addr size
  | Lifted l -> L.mem_unmap l addr size

let mem_protect t addr size perm =
  match t with
  | Unicorn u -> Uc.mem_protect u addr size perm
  | Lifted l -> L.mem_protect l addr size perm

let mem_write t addr data =
  match t with
  | Unicorn u -> Uc.mem_write u addr data
  | Lifted l -> L.mem_write l addr data

let mem_read t addr n =
  match t with
  | Unicorn u -> Uc.mem_read u addr n
  | Lifted l -> L.mem_read l addr n

let mem_regions = function
  | Unicorn u -> Uc.mem_regions u
  | Lifted l -> L.mem_regions l

let set_unmapped t name x =
  match t with Unicorn _ -> () | Lifted l -> L.set_unmapped l name x

let regs = Uc.regs
let reg = Uc.reg

let reg_size t id =
  match t with Unicorn u -> Uc.reg_size u id | Lifted l -> L.reg_size l id

let reg_read t id =
  match t with Unicorn u -> Uc.reg_read u id | Lifted l -> L.reg_read l id

let reg_write t id x =
  match t with
  | Unicorn u -> Uc.reg_write u id x
  | Lifted l -> L.reg_write l id x

let reg_read_bytes t id =
  match t with
  | Unicorn u -> Uc.reg_read_bytes u id
  | Lifted l -> L.reg_read_bytes l id

let reg_write_bytes t id data =
  match t with
  | Unicorn u -> Uc.reg_write_bytes u id data
  | Lifted l -> L.reg_write_bytes l id data

let start ?until ?timeout ?count t pc =
  match t with
  | Unicorn u -> Uc.start ?until ?timeout ?count u pc
  | Lifted l -> L.start ?until ?timeout ?count l pc

let stop = function Unicorn u -> Uc.stop u | Lifted l -> L.stop l
let interrupted = Uc.interrupted
let process_signals = Uc.process_signals

type hook = Unicorn_hook of Uc.hook | Lifted_hook of L.hook | No_hook

type access = Bap_unicorn.access =
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

let on_code ?first ?last t f =
  match t with
  | Unicorn u -> Unicorn_hook (Uc.on_code ?first ?last u f)
  | Lifted l -> Lifted_hook (L.on_code ?first ?last l f)

let on_block ?first ?last t f =
  match t with
  | Unicorn u -> Unicorn_hook (Uc.on_block ?first ?last u f)
  | Lifted l -> Lifted_hook (L.on_block ?first ?last l f)

let on_interrupt t f =
  match t with
  | Unicorn u -> Unicorn_hook (Uc.on_interrupt u f)
  | Lifted l -> Lifted_hook (L.on_interrupt l f)

(* the lifted engine runs no system call, its instructions are
   interpreted, see [on_unsupported] *)
let on_x86_syscall t f =
  match t with
  | Unicorn u -> List.map (fun h -> Unicorn_hook h) (Uc.on_x86_syscall u f)
  | Lifted _ -> []

let on_invalid_insn t f =
  match t with
  | Unicorn u -> Unicorn_hook (Uc.on_invalid_insn u f)
  | Lifted l -> Lifted_hook (L.on_invalid_insn l f)

let on_unsupported t f =
  match t with
  | Unicorn _ -> No_hook
  | Lifted l -> Lifted_hook (L.on_unsupported l f)

let on_mem ?first ?last t accesses f =
  match t with
  | Unicorn u -> Unicorn_hook (Uc.on_mem ?first ?last u accesses f)
  | Lifted l -> Lifted_hook (L.on_mem ?first ?last l accesses f)

let on_mem_invalid ?first ?last t accesses kinds f =
  match t with
  | Unicorn u ->
      Unicorn_hook (Uc.on_mem_invalid ?first ?last u accesses kinds f)
  | Lifted l -> Lifted_hook (L.on_mem_invalid ?first ?last l accesses kinds f)

let delete t h =
  match (t, h) with
  | Unicorn u, Unicorn_hook h -> Uc.delete u h
  | Lifted l, Lifted_hook h -> L.delete l h
  | _, No_hook -> ()
  | _ -> invalid_arg "Bap_engine.delete: the hook is of another engine"

module Trace = Bap_unicorn.Trace

let trace ?first ?last ?memory t trace =
  match t with
  | Unicorn u ->
      List.map (fun h -> Unicorn_hook h) (Uc.trace ?first ?last ?memory u trace)
  | Lifted l ->
      List.map (fun h -> Lifted_hook h) (L.trace ?first ?last ?memory l trace)

type context = Unicorn_context of Uc.context | Lifted_context of L.context

let save = function
  | Unicorn u -> Unicorn_context (Uc.save u)
  | Lifted l -> Lifted_context (L.save l)

let restore t c =
  match (t, c) with
  | Unicorn u, Unicorn_context c -> Uc.restore u c
  | Lifted l, Lifted_context c -> L.restore l c
  | _ -> invalid_arg "Bap_engine.restore: the context is of another engine"
