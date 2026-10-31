import Bap.Core.Memory
import Bap.Bil.Semantics
import Bap.IR.Cfg
import Bap.IR.Optimize
import Bap.Theory.Value
import Bap.Theory.Target
import Bap.Knowledge.Core
import Bap.Graph.Basic
import Bap.Image.Raw
import Bap.Disasm.Basic
import Bap.ABI
import Bap.Primus.Memory
import Bap.Primus.Scheduler
import Bap.Analysis.Validate
import Bap.Analysis.Slice
import Bap.Project.Pass
import Bap.Plugin.Basic
import Bap.API
import Bap.Crypto.KeyWrap
import Bap.Symbolic.Memory
import Bap.LLVM
import Bap.Emu.Semantics
import Bap.Proofs.ABI
import Bap.Proofs.API
import Bap.Proofs.Analysis
import Bap.Proofs.Bil
import Bap.Proofs.Checkpoint
import Bap.Proofs.Core
import Bap.Proofs.Crypto
import Bap.Proofs.Decompile
import Bap.Proofs.Disasm
import Bap.Proofs.Emu
import Bap.Proofs.FFI
import Bap.Proofs.Graph
import Bap.Proofs.IO
import Bap.Proofs.IR
import Bap.Proofs.Image
import Bap.Proofs.Linker
import Bap.Proofs.LinkerAbi
import Bap.Proofs.LinkerImage
import Bap.Proofs.Jit
import Bap.Proofs.Knowledge
import Bap.Proofs.LLVM
import Bap.Proofs.Plugin
import Bap.Proofs.Primus
import Bap.Proofs.Project
import Bap.Proofs.Symbolic
import Bap.Proofs.SmtReader
import Bap.Proofs.Target
import Bap.Proofs.Theory

namespace Bap.Proofs

namespace Core

theorem readByte_empty (address : BitVec 64) :
    Memory.readByte (Memory.empty 64) address = 0 := by
  rfl

theorem readByte_writeByte_same :
    Memory.readByte (Memory.writeByte (Memory.empty 64) (BitVec.ofNat 64 0x1000) 0x42)
      (BitVec.ofNat 64 0x1000) = 0x42 := by
  decide +kernel

end Core

namespace Bil

theorem lookup_bind (env : Bil.Env) (var : Bap.Var) (value : Bap.Value) :
    Bil.lookup (Bil.bind env var value) var = .ok value := by
  simp [Bil.lookup, Bil.bind]

theorem bind_shadow (env : Bil.Env) (var : Bap.Var) (old new : Bap.Value) :
    Bil.lookup (Bil.bind (Bil.bind env var old) var new) var = .ok new := by
  simp [Bil.lookup, Bil.bind]

end Bil

namespace IR

theorem intoSub_fromSub (sub : Bap.IR.Sub) :
    (Bap.IR.Cfg.fromSub sub).intoSub sub = sub := by
  rfl

theorem directTarget_direct (tid : Bap.IR.Tid) :
    (Bap.IR.Label.direct tid).directTarget = some tid := by
  rfl

theorem directTarget_indirect (exp : Bap.Bil.Exp) :
    (Bap.IR.Label.indirect exp).directTarget = none := by
  rfl

end IR

namespace Theory

theorem bits_bitv (width : Nat) : Bap.Theory.ValueSort.bits (.bitv width) = some width := by
  rfl

theorem base_version (var : Bap.Theory.Var) (index : Nat) :
    (var.version index).base = var.base := by
  simp only [Bap.Theory.Var.version]
  split <;> rfl

theorem matches_self (target : Bap.Theory.Target) : target.matches target.name = true := by
  simp [Bap.Theory.Target.matches, Bap.Theory.Target.matching,
    Bap.Theory.namedBy]

end Theory

namespace Knowledge

theorem maxDomain_join (left right : Nat) :
    Bap.Knowledge.maxDomain.join left right = some (max left right) := by
  rfl

theorem lookupFact_empty (slot : Bap.Knowledge.Slot kind) (object : Bap.Knowledge.Object) :
    Bap.Knowledge.lookupFact slot object [] = .ok none := by
  rfl

theorem suggest_version (agent : Bap.Knowledge.Agent) (slot : Bap.Knowledge.Slot kind)
    (object : Bap.Knowledge.Object) (value : kind.data) (state : Bap.Knowledge.State) :
    state.version ≤ (Bap.Knowledge.suggest agent slot object value state).version := by
  simp only [Bap.Knowledge.suggest]
  split <;> simp

end Knowledge

namespace Graphs

theorem subset_self [DecidableEq α] (values : List α) : Bap.Graph.subset values values = true := by
  simp [Bap.Graph.subset]

theorem reachable_edge :
    1 ∈ Bap.Graph.reachable ⟨[0, 1], [(0, 1)]⟩ 0 := by
  decide +kernel

end Graphs

namespace Images

theorem raw_entryPoint (data : ByteArray) (base : Nat) (endian : Bap.Endian) :
    (Bap.Image.Raw.load data base endian).entryPoint = base := by
  rfl

theorem raw_readByte :
    Bap.Image.MemoryMap.readByte (Bap.Image.Raw.load (ByteArray.mk #[0x7f]) 0x1000 .little).memory 0x1000 =
      some 0x7f := by
  decide +kernel

end Images

namespace Disassembly

theorem successors_normal (insn : Bap.Disasm.Insn) (h : insn.flow = .normal) :
    insn.successors = [insn.next] := by
  simp [Bap.Disasm.Insn.successors, h]

theorem successors_conditional (insn : Bap.Disasm.Insn) (h : insn.flow = .conditionalJump) :
    insn.successors = insn.next :: insn.target.toList := by
  simp [Bap.Disasm.Insn.successors, h]

end Disassembly

namespace Targets

theorem aarch64_argument_count :
    (Bap.ABI.convention .aarch64).map (fun abi => abi.functionArguments.length) = some 8 := by
  decide +kernel

theorem aarch64_stack_argument :
    (Bap.ABI.convention .aarch64).map (fun abi => Bap.ABI.argumentLocation abi 8) =
      some (.stack 0) := by
  decide +kernel

end Targets

namespace Primus

theorem region_contains_lower (region : Bap.Primus.Region) (h : region.lower < region.upper) :
    region.contains region.lower = true := by
  simp [Bap.Primus.Region.contains, h]

theorem roundRobin_empty :
    Bap.Primus.Scheduler.roundRobin.next [] 0 0 [] = none := by
  rfl

theorem roundRobin_step :
    Bap.Primus.Scheduler.roundRobin.next [1, 2] 1 0 [] = some 2 := by
  decide +kernel

end Primus

namespace Analyses

theorem validate_ok_true : Bap.Analysis.Validate.ok ⟨true, true, true, true⟩ = true := by
  rfl

theorem validate_empty_program :
    Bap.Analysis.Validate.compare [] [] [] {} = .ok ⟨true, true, true, true⟩ := by
  rfl

end Analyses

namespace Plugins

theorem runPasses_empty (project : Bap.Project.Project) :
    Bap.Project.runPasses [] project = .ok project := by
  rfl

theorem defaultRegistry_has_summarize :
    (Bap.Plugin.defaultRegistry.findPass "summarize").map Bap.Project.Pass.name = some "summarize" := by
  decide +kernel

end Plugins

namespace CLI

theorem argumentLocations_length (abi : Bap.ABI.Convention) (prototype : Bap.API.Prototype) :
    (Bap.API.argumentLocations abi prototype).length = prototype.params.length := by
  simp [Bap.API.argumentLocations]

end CLI

namespace Crypto

theorem aes128_fips197 :
    (Bap.Crypto.AES.decryptBlock
      (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
      (ByteArray.mk #[0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a])).toOption =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) := by
  decide +kernel

theorem rfc3394_vector1 :
    (Bap.Crypto.KeyWrap.unwrap
      (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
      (ByteArray.mk #[0x1f,0xa6,0x8b,0x0a,0x81,0x12,0xb4,0x47,0xae,0xf3,0x4b,0xd8,0xfb,0x5a,0x7b,0x82,0x9d,0x3e,0x86,0x23,0x71,0xd2,0xcf,0xe5])).toOption =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) := by
  decide +kernel

end Crypto

namespace Symbolic

theorem width_concat (left right : Bap.Symbolic.Expr) :
    (Bap.Symbolic.Expr.concat left right).width = left.width + right.width := by
  rfl

theorem readByte_writeByte_same (memory : Bap.Symbolic.Memory) (address value : Bap.Symbolic.Expr) :
    (memory.writeByte address value).readByte address = value := by
  simp [Bap.Symbolic.Memory.readByte, Bap.Symbolic.Memory.writeByte]

end Symbolic

namespace LLVM

theorem decoded_size (assembly : String) (size flags : Nat) (opcode : String) (operands : List Bap.LLVM.Operand) :
    (⟨assembly, size, flags, opcode, operands⟩ : Bap.LLVM.Decoded).size = size := by
  rfl

theorem mcOperand_equality : (Bap.LLVM.MCOperand.imm 1) = (Bap.LLVM.MCOperand.imm 1) := by
  rfl

end LLVM

end Bap.Proofs
