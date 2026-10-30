import Bap.LLVM

namespace Bap.Proofs.LLVM

open Bap.LLVM

/-! The FFI entry points of `Bap.LLVM` are opaque. What can be proved is that the Lean wrappers
transport their results faithfully, in any world state, and that the data types are lawful. -/

/-- Interpretation of a raw textual disassembly tuple. -/
def ofRaw : String × Nat × Nat × String × List Operand → Decoded
  | (assembly, size, flags, opcode, operands) => ⟨assembly, size, flags, opcode, operands⟩

/-- Raw tuple of a textual disassembly. -/
def toRaw (decoded : Decoded) : String × Nat × Nat × String × List Operand :=
  (decoded.assembly, decoded.size, decoded.flags, decoded.opcode, decoded.operands)

theorem ofRaw_toRaw (decoded : Decoded) : ofRaw (toRaw decoded) = decoded := rfl

theorem toRaw_ofRaw (raw : String × Nat × Nat × String × List Operand) :
    toRaw (ofRaw raw) = raw := rfl

theorem ofRaw_injective (a b : String × Nat × Nat × String × List Operand)
    (h : ofRaw a = ofRaw b) : a = b := by
  rw [← toRaw_ofRaw a, ← toRaw_ofRaw b, h]

/-- `disassemble` succeeds exactly when the FFI call does, with the decoded raw tuple, and does
not touch the world beyond it. -/
theorem disassemble_ok_iff (triple : String) (data : ByteArray) (address : Nat) (s s')
    (decoded : Decoded) :
    disassemble triple data address s = EST.Out.ok decoded s' ↔
      disassembleRaw triple data address s = EST.Out.ok (toRaw decoded) s' := by
  have hrun : disassemble triple data address s =
      EST.bind (disassembleRaw triple data address) (fun raw => EST.pure (ofRaw raw)) s := rfl
  rw [hrun]
  unfold EST.bind
  cases h : disassembleRaw triple data address s with
  | ok raw s1 =>
    simp only [EST.pure, EST.Out.ok.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨toRaw_ofRaw raw, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨ofRaw_toRaw decoded, rfl⟩
  | error e s1 => simp

/-- FFI failures pass through `disassemble` unchanged. -/
theorem disassemble_error_iff (triple : String) (data : ByteArray) (address : Nat) (s s')
    (error : IO.Error) :
    disassemble triple data address s = EST.Out.error error s' ↔
      disassembleRaw triple data address s = EST.Out.error error s' := by
  have hrun : disassemble triple data address s =
      EST.bind (disassembleRaw triple data address) (fun raw => EST.pure (ofRaw raw)) s := rfl
  rw [hrun]
  unfold EST.bind
  cases h : disassembleRaw triple data address s with
  | ok raw s1 => simp [EST.pure]
  | error e s1 => simp

/-- The size, flags and operands reported by `disassemble` are the FFI's own. -/
theorem disassemble_fields (triple : String) (data : ByteArray) (address : Nat) (s s')
    (decoded : Decoded) (h : disassemble triple data address s = EST.Out.ok decoded s') :
    ∃ assembly opcode, disassembleRaw triple data address s = EST.Out.ok
      (assembly, decoded.size, decoded.flags, opcode, decoded.operands) s' ∧
      decoded.assembly = assembly ∧ decoded.opcode = opcode :=
  ⟨_, _, (disassemble_ok_iff _ _ _ _ _ _).1 h, rfl, rfl⟩

/-- Interpretation of a raw machine-instruction disassembly tuple. -/
def ofRawMC : String × Nat × Nat × MCInst → MCDecoded
  | (assembly, size, flags, instruction) => ⟨assembly, size, flags, instruction⟩

/-- Raw tuple of a machine-instruction disassembly. -/
def toRawMC (decoded : MCDecoded) : String × Nat × Nat × MCInst :=
  (decoded.assembly, decoded.size, decoded.flags, decoded.instruction)

theorem ofRawMC_toRawMC (decoded : MCDecoded) : ofRawMC (toRawMC decoded) = decoded := rfl

theorem toRawMC_ofRawMC (raw : String × Nat × Nat × MCInst) : toRawMC (ofRawMC raw) = raw := rfl

theorem disassembleMC_ok_iff (triple : String) (data : ByteArray) (address : Nat) (s s')
    (decoded : MCDecoded) :
    disassembleMC triple data address s = EST.Out.ok decoded s' ↔
      disassembleMCRaw triple data address s = EST.Out.ok (toRawMC decoded) s' := by
  have hrun : disassembleMC triple data address s =
      EST.bind (disassembleMCRaw triple data address) (fun raw => EST.pure (ofRawMC raw)) s := rfl
  rw [hrun]
  unfold EST.bind
  cases h : disassembleMCRaw triple data address s with
  | ok raw s1 =>
    simp only [EST.pure, EST.Out.ok.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨toRawMC_ofRawMC raw, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨ofRawMC_toRawMC decoded, rfl⟩
  | error e s1 => simp

theorem disassembleMC_error_iff (triple : String) (data : ByteArray) (address : Nat) (s s')
    (error : IO.Error) :
    disassembleMC triple data address s = EST.Out.error error s' ↔
      disassembleMCRaw triple data address s = EST.Out.error error s' := by
  have hrun : disassembleMC triple data address s =
      EST.bind (disassembleMCRaw triple data address) (fun raw => EST.pure (ofRawMC raw)) s := rfl
  rw [hrun]
  unfold EST.bind
  cases h : disassembleMCRaw triple data address s with
  | ok raw s1 => simp [EST.pure]
  | error e s1 => simp

/-- The FFI's success or failure on one call does not depend on anything but its result: wrappers
over the same raw outcome agree, so a wrapper call never fabricates a decoding. -/
theorem disassemble_congr (t t' : String) (d d' : ByteArray) (a a' : Nat) (s)
    (h : disassembleRaw t d a s = disassembleRaw t' d' a' s) :
    disassemble t d a s = disassemble t' d' a' s := by
  have hrun : ∀ t d a, disassemble t d a s =
      EST.bind (disassembleRaw t d a) (fun raw => EST.pure (ofRaw raw)) s := fun _ _ _ => rfl
  rw [hrun, hrun]
  unfold EST.bind
  rw [h]

/-! ## Operands -/

/-- Immediate value of a textual operand. -/
def immOf : Operand → Option Int
  | .imm value => some value
  | .reg _ => none

/-- Register name of a textual operand. -/
def regOf : Operand → Option String
  | .reg name => some name
  | .imm _ => none

/-- A textual operand is exactly a register or an immediate, and each view determines it. -/
theorem operand_views (operand : Operand) :
    (∃ name, regOf operand = some name ∧ immOf operand = none ∧ operand = .reg name) ∨
      (∃ value, immOf operand = some value ∧ regOf operand = none ∧ operand = .imm value) := by
  cases operand with
  | reg name => exact .inl ⟨name, rfl, rfl, rfl⟩
  | imm value => exact .inr ⟨value, rfl, rfl, rfl⟩

theorem operand_eq_of_views (a b : Operand) (h1 : regOf a = regOf b) (h2 : immOf a = immOf b) :
    a = b := by
  cases a <;> cases b <;> simp_all [regOf, immOf]

end Bap.Proofs.LLVM
