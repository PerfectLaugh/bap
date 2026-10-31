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
import Bap.API
import Bap.Crypto.KeyWrap
import Bap.Symbolic.Memory
import Bap.LLVM
import Bap.Emu.Semantics
import Bap.Proofs.ABI
import Bap.Proofs.API
import Bap.Proofs.Analysis
import Bap.Proofs.Bil
import Bap.Proofs.Binary
import Bap.Proofs.Checkpoint
import Bap.Proofs.ConstProp
import Bap.Proofs.Core
import Bap.Proofs.Crypto
import Bap.Proofs.CryptoVectors
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
import Bap.Proofs.Primus
import Bap.Proofs.PrimusRelated
import Bap.Proofs.PrimusBisim
import Bap.Proofs.PrimusLoad
import Bap.Proofs.PrimusAddress
import Bap.Proofs.Project
import Bap.Proofs.Symbolic
import Bap.Proofs.SmtReader
import Bap.Proofs.Target
import Bap.Proofs.Theory
import Bap.Proofs.X86Memo

/-! # What the proofs rest on

This is everything in the project that is trusted, or only tested, and not proved. Every other claim is a theorem whose
`#print axioms` is `propext`, `Classical.choice` and `Quot.sound`. A file and line says where each is written down at more length.

## Trusted: outside of what Lean can see

1. **Lean itself.** The kernel, and for the running program the compiler and the runtime: the theorems are about the definitions, not the generated code (Bap/Proofs/Crypto.lean:1518). A `@[csimp]` swap is a theorem; `@[extern]` is an `opaque` that nothing can unfold.
2. **The native code of the JIT**, `native/bap_jit.cpp` and LLVM's code generation: obligations 1 to 10 (Bap/Jit.lean:1). `Bap.Proofs.Jit` proves the Lean side against them on a model.
3. **The emulator's plumbing in `IO`**: refs, `save` and `restore`, `IO.asTask`, the mutex of hooks (Bap/Emu/Core.lean:13, items 1, 2, 4 and 5).
4. **`NativeRange`**: what a native run of a range does, by reading `runBlockObserved` (Bap/Emu/CoreProofs.lean:2796, Bap/Emu/Core.lean:26). `rangeLaws_real` and `restartLaws_real` follow from it.
5. **LLVM's decoder and assembler** (Bap/LLVM.lean:16, Bap/Proofs/LLVM.lean:7). What instruction the bytes are, and that the same bytes are the same instruction (Bap/Emu/Core.lean:37), is what LLVM says. The wrappers are proved to pass it on, not that it is right.
6. **Z3's answers** (Bap/FFI/Z3.lean:5, Bap/Proofs/FFI.lean:19). What is sent and how the answer is read are proved.
7. **Refs and files around lifting.** A cached environment (Bap/Target/LLVMLift.lean:507) and the memo of x86 code (Bap/Target/LLVMLift.lean:1289) hand back what was put in them: `x86MemoStep_sound` (Bap/Proofs/X86Memo.lean:83) is about the pure step between the read and the write, as Lean can't see a ref. The semantics are the files on disk (Bap/Target/LLVMLift.lean:454).
8. **Standards read by a person.** That `Spec` says what FIPS-197 and RFC 3394 say is by reading, with their printed vectors checked by the kernel (Bap/Proofs/Crypto.lean:837, Bap/Proofs/Crypto.lean:1511). The formats of ELF, PE, COFF and DWARF are the same: what is proved is of the parsers as written, against no text of the standards.

## Modelled, not proved of a machine

9. **That the Lisp semantics are what the hardware does.** Lifting is proved to mean the Lisp source (Bap/Proofs/PrimusLoad.lean:290), so the source is where the ISA is trusted; `BapTests` runs instructions against expected values, on samples.
10. **Masked EVEX sources that no lane owns** (semantics/x86/x86-avx512.lisp:219): VPERM*, VPERMI2*, VPERMT2*, VALIGN*, VPALIGNR, VDBPSADBW, VPCONFLICT* and the count of VPSLL* and its kin load only if some lane is let through. This rests on a load having no effect but its fault, and on faults of these not being modelled (semantics/x86/x86-avx512.lisp:162), and not on the SDM, which isn't here; LLVM's tables say nothing of fault suppression. The values are the same either way (BapTests/LLVM.lean:1806). If the SDM's class for one of these is "no fault suppression", as is remembered of them, hardware would fault where this doesn't, with a masked lane on an unmapped page.
11. **What each target leaves out**, each as a comment where it is: x86 exceptions (semantics/x86/x86-avx512.lisp:162) and `x86-sse-intrinsics.lisp` (semantics/x86/x86-sse-intrinsics.lisp:14 on); reservations and FPSCR on PowerPC (semantics/powerpc/powerpc.lisp:621 on); reservations and hardware registers on MIPS (semantics/mips/mips.lisp:261 on); the exclusive monitor on ARM (semantics/arm/arm-a32-mem.lisp:170, semantics/arm/thumb2.lisp:244); AArch64 (semantics/arm/aarch64-special.lisp:39 on, semantics/arm/aarch64-float.lisp:11); extensions and counters on RISC-V (semantics/riscv/riscv.lisp:1503).
12. **Callees in the analyses and the IR**: a call is taken to leave the environment as it is (Bap/Analysis/Slice.lean:384, Bap/Proofs/IR.lean:2572).

## Premises of theorems

These aren't trusted, but a theorem says nothing where they fail.

13. `propagateConstants_fromSub` (Bap/Proofs/ConstProp.lean:2032) needs the blocks of a function to have different ids. Two blocks of one id can differ: `isSolved` of the unrestricted analysis fails and the restricted one's may not.
14. `Bap.Proofs.Analysis` (Bap/Proofs/Analysis.lean:3201, Bap/Proofs/Analysis.lean:4929), and writes that don't wrap around the address space in `Bap.Proofs.Symbolic` (Bap/Proofs/Symbolic.lean:3271), which says what happens if they do.

## Tested, not proved

15. **The reader of SMT scripts on concrete text** (Bap/Proofs/SmtReader.lean:4): deliberately tested and not `decide`d, for the time it would take. Its laws are proved.
16. **`BapTests` as a whole, for what its comparisons go beyond the theorems**: goldens of real binaries and the comparisons with upstream's output. Anything a theorem also says, as `propagateConstants` against its specification, is only a check that the two stay connected.

Constant propagation with only what can be read (`propagateConstants_unrestricted`) and the x86 memo (`x86MemoStep_sound`, `apply_anywhere`) were on this list until they were proved. -/

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

namespace Passes

theorem runPasses_empty (project : Bap.Project.Project) :
    Bap.Project.runPasses [] project = .ok project := by
  rfl

end Passes

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
