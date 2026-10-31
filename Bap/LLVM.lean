namespace Bap.LLVM

inductive Operand where
  | reg (name : String)
  | imm (value : Int)
  deriving Repr, DecidableEq

structure Decoded where
  assembly : String
  size : Nat
  flags : Nat
  opcode : String
  operands : List Operand
  deriving Repr

@[extern "bap_llvm_assemble"]
opaque assemble (triple source : String) : IO ByteArray

@[extern "bap_llvm_disassemble"]
opaque disassembleRaw (triple : String) (data : ByteArray) (address : Nat) :
  IO (String × Nat × Nat × String × List Operand)

def disassemble (triple : String) (data : ByteArray) (address : Nat := 0) : IO Decoded := do
  let (assembly, size, flags, opcode, operands) ← disassembleRaw triple data address
  pure ⟨assembly, size, flags, opcode, operands⟩

opaque MCInst : Type

inductive MCOperand where
  | reg (id : Nat)
  | imm (value : Int)
  deriving Repr, DecidableEq

structure MCDecoded where
  assembly : String
  size : Nat
  flags : Nat
  instruction : MCInst

@[extern "bap_llvm_disassemble_mc"]
opaque disassembleMCRaw (triple : String) (data : ByteArray) (address : Nat) :
  IO (String × Nat × Nat × MCInst)

@[extern "bap_llvm_mc_opcode"]
opaque mcOpcode (instruction : MCInst) : Nat

@[extern "bap_llvm_mc_operands"]
opaque mcOperands (instruction : MCInst) : IO (List MCOperand)

@[extern "bap_llvm_opcode_id"]
opaque opcodeId (triple name : String) : IO Nat

@[extern "bap_llvm_opcode_id_opt"]
opaque opcodeId? (triple name : String) : IO (Option Nat)

@[extern "bap_llvm_register_id"]
opaque registerId (triple name : String) : IO Nat

@[extern "bap_llvm_register_names"]
opaque registerNames (triple : String) : IO (List (Nat × String))

def disassembleMC (triple : String) (data : ByteArray) (address : Nat := 0) : IO MCDecoded := do
  let (assembly, size, flags, instruction) ← disassembleMCRaw triple data address
  pure ⟨assembly, size, flags, instruction⟩

end Bap.LLVM
