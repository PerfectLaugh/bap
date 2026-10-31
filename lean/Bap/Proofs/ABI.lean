import Lean.Elab.Term
import Bap.ABI

namespace Bap.Proofs.ABI

open Bap.ABI

open Lean Elab Term in
/-- Names a private constant of another module: `priv% Module Full.Name`. -/
local elab "priv% " mod:ident n:ident : term => do
  return mkConst (mkPrivateNameCore mod.getId n.getId)

private abbrev reg : String → Nat → Bap.Var := priv% Bap.ABI Bap.ABI.reg
private abbrev regs : Nat → List String → List Bap.Var := priv% Bap.ABI Bap.ABI.regs
private abbrev numbered : String → Nat → Nat → Nat → List Bap.Var := priv% Bap.ABI Bap.ABI.numbered
private abbrev x86 : Convention := priv% Bap.ABI Bap.ABI.x86
private abbrev x86_64 : Convention := priv% Bap.ABI Bap.ABI.x86_64
private abbrev riscv : Nat → Convention := priv% Bap.ABI Bap.ABI.riscv
private abbrev aarch64 : Convention := priv% Bap.ABI Bap.ABI.aarch64
private abbrev mips : Nat → Convention := priv% Bap.ABI Bap.ABI.mips
private abbrev arm : Convention := priv% Bap.ABI Bap.ABI.arm
private abbrev powerpc : Nat → Convention := priv% Bap.ABI Bap.ABI.powerpc
private abbrev systemz : Convention := priv% Bap.ABI Bap.ABI.systemz

/-! ## Argument placement for an arbitrary convention -/

theorem argumentLocation_of_lt (abi : Convention) (index : Nat)
    (h : index < abi.functionArguments.length) :
    argumentLocation abi index = .register abi.functionArguments[index] := by
  simp [argumentLocation, List.getElem?_eq_getElem h]

theorem argumentLocation_of_ge (abi : Convention) (index : Nat)
    (h : abi.functionArguments.length ≤ index) :
    argumentLocation abi index =
      .stack ((index - abi.functionArguments.length) * (abi.wordSize / 8)) := by
  simp [argumentLocation, List.getElem?_eq_none h]

/-- The register/stack split is exactly at the length of the register list. -/
theorem argumentLocation_isRegister_iff (abi : Convention) (index : Nat) :
    (∃ var, argumentLocation abi index = .register var) ↔ index < abi.functionArguments.length := by
  constructor
  · rintro ⟨var, hv⟩
    refine Nat.lt_of_not_le fun hle => ?_
    rw [argumentLocation_of_ge abi index hle] at hv
    cases hv
  · intro h
    exact ⟨_, argumentLocation_of_lt abi index h⟩

theorem argumentLocation_isStack_iff (abi : Convention) (index : Nat) :
    (∃ offset, argumentLocation abi index = .stack offset) ↔
      abi.functionArguments.length ≤ index := by
  constructor
  · rintro ⟨offset, hv⟩
    refine Nat.le_of_not_lt fun hlt => ?_
    rw [argumentLocation_of_lt abi index hlt] at hv
    cases hv
  · intro h
    exact ⟨_, argumentLocation_of_ge abi index h⟩

/-- Each register argument location holds a register of the convention. -/
theorem argumentLocation_register_mem (abi : Convention) (index : Nat) (var : Bap.Var)
    (h : argumentLocation abi index = .register var) : var ∈ abi.functionArguments := by
  have hlt := (argumentLocation_isRegister_iff abi index).1 ⟨var, h⟩
  rw [argumentLocation_of_lt abi index hlt] at h
  cases h
  exact List.getElem_mem hlt

/-- Every register of the convention is used, by its own position. -/
theorem argumentLocation_surjective_registers (abi : Convention) (var : Bap.Var)
    (h : var ∈ abi.functionArguments) : ∃ index, argumentLocation abi index = .register var := by
  have ⟨i, hi, he⟩ := List.getElem_of_mem h
  exact ⟨i, by rw [argumentLocation_of_lt abi i hi, he]⟩

/-- The stack slots advance by one word per argument. -/
theorem stack_offset_succ (abi : Convention) (index offset : Nat)
    (h : argumentLocation abi index = .stack offset) :
    argumentLocation abi (index + 1) = .stack (offset + abi.wordSize / 8) := by
  have hle := (argumentLocation_isStack_iff abi index).1 ⟨offset, h⟩
  rw [argumentLocation_of_ge abi index hle] at h
  rw [argumentLocation_of_ge abi (index + 1) (by omega)]
  cases h
  rw [Nat.sub_add_comm hle, Nat.add_mul, Nat.one_mul]

/-- The first overflowing argument sits at offset zero. -/
theorem first_stack_argument (abi : Convention) :
    argumentLocation abi abi.functionArguments.length = .stack 0 := by
  rw [argumentLocation_of_ge abi _ (Nat.le_refl _)]
  simp

/-- Later stack arguments get strictly higher, non-overlapping word-sized slots. -/
theorem stack_slots_disjoint (abi : Convention) (i j a b : Nat) (hij : i < j)
    (hi : argumentLocation abi i = .stack a) (hj : argumentLocation abi j = .stack b) :
    a + abi.wordSize / 8 ≤ b := by
  have hle := (argumentLocation_isStack_iff abi i).1 ⟨a, hi⟩
  rw [argumentLocation_of_ge abi i hle] at hi
  rw [argumentLocation_of_ge abi j (by omega)] at hj
  cases hi
  cases hj
  have hstep : (i - abi.functionArguments.length + 1) ≤ j - abi.functionArguments.length := by omega
  calc (i - abi.functionArguments.length) * (abi.wordSize / 8) + abi.wordSize / 8
      = (i - abi.functionArguments.length + 1) * (abi.wordSize / 8) := by
        rw [Nat.add_mul, Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hstep

/-- Stack offsets are monotone in the argument index. -/
theorem stack_offset_mono (abi : Convention) (i j a b : Nat) (hij : i ≤ j)
    (hi : argumentLocation abi i = .stack a) (hj : argumentLocation abi j = .stack b) : a ≤ b := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have := stack_slots_disjoint abi i j a b hlt hi hj
    omega
  · rw [hi] at hj
    cases hj
    exact Nat.le_refl _

/-- Distinct arguments never share a location if registers are distinct and words are non-empty. -/
theorem argumentLocation_injective (abi : Convention) (hn : abi.functionArguments.Nodup)
    (hw : 8 ≤ abi.wordSize) (i j : Nat)
    (h : argumentLocation abi i = argumentLocation abi j) : i = j := by
  have hbyte : 0 < abi.wordSize / 8 := Nat.div_pos hw (by omega)
  by_cases hi : i < abi.functionArguments.length <;> by_cases hj : j < abi.functionArguments.length
  · rw [argumentLocation_of_lt abi i hi, argumentLocation_of_lt abi j hj] at h
    have he := Location.register.inj h
    have hp := List.pairwise_iff_getElem.1 hn
    rcases Nat.lt_trichotomy i j with hlt | heq | hlt
    · exact absurd he (hp i j hi hj hlt)
    · exact heq
    · exact absurd he.symm (hp j i hj hi hlt)
  · rw [argumentLocation_of_lt abi i hi, argumentLocation_of_ge abi j (by omega)] at h
    cases h
  · rw [argumentLocation_of_ge abi i (by omega), argumentLocation_of_lt abi j hj] at h
    cases h
  · have hi' := Nat.le_of_not_lt hi
    have hj' := Nat.le_of_not_lt hj
    rw [argumentLocation_of_ge abi i hi', argumentLocation_of_ge abi j hj'] at h
    have := Nat.eq_of_mul_eq_mul_right hbyte (Location.stack.inj h)
    omega

/-! ## `alignStack` -/

theorem alignStack_le (alignment address : Nat) : alignStack alignment address ≤ address := by
  unfold alignStack
  split
  · exact Nat.le_refl _
  · exact Nat.div_mul_le_self _ _

theorem alignStack_dvd (alignment address : Nat) (h : alignment ≠ 0) :
    alignment ∣ alignStack alignment address := by
  simp only [alignStack, h, ite_false]
  exact Nat.dvd_mul_left _ _

/-- The alignment moves the stack down by less than one alignment unit. -/
theorem alignStack_gap (alignment address : Nat) (h : alignment ≠ 0) :
    address - alignStack alignment address < alignment := by
  simp only [alignStack, h, ite_false]
  have h1 := Nat.div_add_mod address alignment
  have h2 : address % alignment < alignment := Nat.mod_lt _ (Nat.pos_of_ne_zero h)
  have h3 : address / alignment * alignment = alignment * (address / alignment) := Nat.mul_comm _ _
  omega

/-- `alignStack` picks the largest aligned address not above the input. -/
theorem alignStack_greatest (alignment address candidate : Nat) (h : alignment ≠ 0)
    (hd : alignment ∣ candidate) (hle : candidate ≤ address) :
    candidate ≤ alignStack alignment address := by
  simp only [alignStack, h, ite_false]
  have ⟨k, hk⟩ := hd
  subst hk
  have hpos := Nat.pos_of_ne_zero h
  have : k ≤ address / alignment := (Nat.le_div_iff_mul_le hpos).2 (by rwa [Nat.mul_comm] at hle)
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ this

theorem alignStack_idempotent (alignment address : Nat) :
    alignStack alignment (alignStack alignment address) = alignStack alignment address := by
  unfold alignStack
  split
  · rfl
  · rename_i h
    rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero h)]

theorem alignStack_eq_self_iff (alignment address : Nat) (h : alignment ≠ 0) :
    alignStack alignment address = address ↔ alignment ∣ address := by
  constructor
  · intro he
    exact he ▸ alignStack_dvd alignment address h
  · intro hd
    exact Nat.le_antisymm (alignStack_le _ _) (alignStack_greatest _ _ _ h hd (Nat.le_refl _))

theorem alignStack_mono (alignment a b : Nat) (h : a ≤ b) :
    alignStack alignment a ≤ alignStack alignment b := by
  unfold alignStack
  split
  · exact h
  · exact Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

/-! ## The per-architecture conventions -/

/-- Name-level sanity of a convention, as a computable check. -/
def namesOk (c : Convention) : Bool :=
  let args := c.functionArguments.map (·.name)
  let sys := c.syscallArguments.map (·.name)
  decide args.Nodup && decide sys.Nodup &&
    !args.contains c.stackPointer.name && !sys.contains c.stackPointer.name &&
    !sys.contains c.syscallNumber.name && c.result.name != c.stackPointer.name &&
    match c.returnAddress with
    | none => true
    | some ra => !args.contains ra.name && !sys.contains ra.name && ra.name != c.stackPointer.name &&
      ra.name != c.result.name

private theorem namesOk_x86 : namesOk x86 = true := rfl
private theorem namesOk_x86_64 : namesOk x86_64 = true := rfl
private theorem namesOk_riscv (w) : namesOk (riscv w) = true := rfl
private theorem namesOk_aarch64 : namesOk aarch64 = true := rfl
private theorem mips_args (w : Nat) :
    (mips w).functionArguments = numbered "R" w 4 (if w = 32 then 7 else 11) := rfl

private theorem namesOk_mips (w) : namesOk (mips w) = true := by
  by_cases h : w = 32
  · subst h
    rfl
  · have hshape : mips w = { (mips w) with functionArguments := numbered "R" w 4 11 } := by
      rw [show (numbered "R" w 4 11) = (mips w).functionArguments by
        rw [mips_args, ite_eq_right h]]
    rw [hshape]
    rfl
private theorem namesOk_arm : namesOk arm = true := rfl
private theorem namesOk_powerpc (w) : namesOk (powerpc w) = true := rfl
private theorem namesOk_systemz : namesOk systemz = true := rfl

/-- Conventions exist for all known architectures. -/
theorem convention_isSome_iff (arch : Image.Arch) (w : Nat) :
    (convention arch w).isSome ↔ arch ≠ .unknown := by
  cases arch <;> simp [convention]

/-- All register-name facts, for every architecture and every requested word size. -/
theorem convention_namesOk (arch : Image.Arch) (w : Nat) (c : Convention)
    (h : convention arch w = some c) : namesOk c = true := by
  cases arch <;> simp only [convention, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact namesOk_x86
  · exact namesOk_x86_64
  · exact namesOk_arm
  · exact namesOk_aarch64
  · exact namesOk_mips w
  · exact namesOk_powerpc w
  · exact namesOk_riscv w
  · exact namesOk_systemz

/-- What `namesOk` guarantees. -/
structure RegisterFacts (c : Convention) : Prop where
  argsNodup : (c.functionArguments.map (·.name)).Nodup
  syscallNodup : (c.syscallArguments.map (·.name)).Nodup
  spNotArg : c.stackPointer.name ∉ c.functionArguments.map (·.name)
  spNotSyscallArg : c.stackPointer.name ∉ c.syscallArguments.map (·.name)
  numberNotSyscallArg : c.syscallNumber.name ∉ c.syscallArguments.map (·.name)
  resultNotSp : c.result.name ≠ c.stackPointer.name
  returnAddress : ∀ ra ∈ c.returnAddress, ra.name ≠ c.stackPointer.name ∧ ra.name ≠ c.result.name ∧
    ra.name ∉ c.functionArguments.map (·.name) ∧ ra.name ∉ c.syscallArguments.map (·.name)

theorem RegisterFacts.of_namesOk (c : Convention) (h : namesOk c = true) : RegisterFacts c := by
  obtain ⟨wordSize, functionArguments, result, syscallNumber, syscallArguments, stackPointer, ra⟩ := c
  cases ra with
  | none =>
    simp only [namesOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_true,
      bne_iff_ne, ne_eq, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, by simp⟩
  | some ra =>
    simp only [namesOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      bne_iff_ne, ne_eq, List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, ⟨⟨⟨h7, h8⟩, h9⟩, h10⟩⟩ := h
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    intro r hr
    cases hr
    exact ⟨h9, h10, h7, h8⟩

theorem convention_registerFacts (arch : Image.Arch) (w : Nat) (c : Convention)
    (h : convention arch w = some c) : RegisterFacts c :=
  .of_namesOk c (convention_namesOk arch w c h)

/-! ### Register-list construction -/

private theorem numbered_eq (name : String) (width first last : Nat) :
    numbered name width first last = (List.range (last - first + 1)).map fun index =>
      (⟨s!"{name}{first + index}", .imm width, 0, false⟩ : Bap.Var) := rfl

theorem numbered_length (name : String) (width first last : Nat) :
    (numbered name width first last).length = last - first + 1 := by
  simp [numbered_eq]

theorem mem_numbered_iff (name : String) (width first last : Nat) (var : Bap.Var) :
    var ∈ numbered name width first last ↔
      ∃ n, first ≤ n ∧ n ≤ first + (last - first) ∧
        var = ⟨s!"{name}{n}", .imm width, 0, false⟩ := by
  rw [numbered_eq]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨first + i, by omega, by omega, rfl⟩
  · rintro ⟨n, h1, h2, rfl⟩
    refine ⟨n - first, by omega, ?_⟩
    rw [Nat.add_sub_cancel' h1]

private theorem numberedName_inj (name : String) (a b : Nat)
    (h : s!"{name}{a}" = s!"{name}{b}") : a = b := by
  have h' : toString name ++ toString a = toString name ++ toString b := h
  exact Nat.repr_inj.1 ((String.append_right_inj _).1 h')

/-- Numbered register lists never repeat a name, for any prefix and range. -/
theorem numbered_names_nodup (name : String) (width first last : Nat) :
    ((numbered name width first last).map (·.name)).Nodup := by
  rw [numbered_eq, List.map_map]
  refine List.pairwise_map.2 (List.Pairwise.imp ?_ List.nodup_range)
  intro a b hne h
  have := numberedName_inj name _ _ h
  omega

theorem regs_typed (width : Nat) (names : List String) :
    ∀ v ∈ regs width names, v.typ = .imm width := by
  intro v hv
  have hv' : v ∈ names.map fun name => (⟨name, .imm width, 0, false⟩ : Bap.Var) := hv
  rcases List.mem_map.1 hv' with ⟨_, _, rfl⟩
  rfl

theorem numbered_typed (name : String) (width first last : Nat) :
    ∀ v ∈ numbered name width first last, v.typ = .imm width := by
  intro v hv
  rcases (mem_numbered_iff _ _ _ _ _).1 hv with ⟨_, _, _, rfl⟩
  rfl

/-! ### Tables and typing -/

/-- The expected number of argument registers on each architecture. -/
def argumentRegisterCount (arch : Image.Arch) (w : Nat) : Nat :=
  match arch with
  | .x86 => 0
  | .x86_64 => 6
  | .arm => 4
  | .aarch64 => 8
  | .mips => if w = 32 then 4 else 8
  | .powerpc => 8
  | .riscv => 8
  | .systemz => 5
  | .unknown => 0

/-- The architectural word size: fixed, or the requested one on multi-width architectures. -/
def expectedWordSize (arch : Image.Arch) (w : Nat) : Nat :=
  match arch with
  | .x86_64 | .aarch64 | .systemz => 64
  | .arm | .x86 => 32
  | _ => w

/-- Names of the argument registers on each architecture. -/
def argumentNames (arch : Image.Arch) (w : Nat) : List String :=
  match arch with
  | .x86_64 => ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
  | .arm => ["R0", "R1", "R2", "R3"]
  | .aarch64 => ["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"]
  | .mips =>
    if w = 32 then ["R4", "R5", "R6", "R7"]
    else ["R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11"]
  | .powerpc => ["R3", "R4", "R5", "R6", "R7", "R8", "R9", "R10"]
  | .riscv => ["X10", "X11", "X12", "X13", "X14", "X15", "X16", "X17"]
  | .systemz => ["R2", "R3", "R4", "R5", "R6"]
  | _ => []

/-- The stack pointer and return register of each architecture, by the names of its lifter. -/
def controlNames : Image.Arch → Option (String × Option String)
  | .x86 => some ("ESP", none)
  | .x86_64 => some ("RSP", none)
  | .arm => some ("SP", some "LR")
  | .aarch64 => some ("SP", some "X30")
  | .mips => some ("R29", some "R31")
  | .powerpc => some ("R1", some "LR")
  | .riscv => some ("X2", some "X1")
  | .systemz => some ("R15", some "R14")
  | .unknown => none

/-- All registers of a convention have the type of its word. -/
structure WellTyped (c : Convention) : Prop where
  args : ∀ v ∈ c.functionArguments, v.typ = .imm c.wordSize
  syscall : ∀ v ∈ c.syscallArguments, v.typ = .imm c.wordSize
  result : c.result.typ = .imm c.wordSize
  number : c.syscallNumber.typ = .imm c.wordSize
  sp : c.stackPointer.typ = .imm c.wordSize
  ra : ∀ v ∈ c.returnAddress, v.typ = .imm c.wordSize

/-- Fixed shape of a convention produced for `arch`. -/
structure Shape (arch : Image.Arch) (w : Nat) (c : Convention) : Prop where
  word : c.wordSize = expectedWordSize arch w
  names : c.functionArguments.map (·.name) = argumentNames arch w
  control : controlNames arch = some (c.stackPointer.name, c.returnAddress.map (·.name))
  syscallCount : c.syscallArguments.length = 6
  typed : WellTyped c

private theorem ra_none {P : Bap.Var → Prop} : ∀ v ∈ (none : Option Bap.Var), P v := by simp

private theorem ra_some {u : Bap.Var} {w : Nat} (h : u.typ = .imm w) :
    ∀ v ∈ some u, v.typ = .imm w := by
  intro v hv
  cases hv
  exact h

private theorem nil_typed {P : Bap.Var → Prop} : ∀ v ∈ ([] : List Bap.Var), P v := by simp

private theorem mips_names (w : Nat) :
    (mips w).functionArguments.map (·.name) = argumentNames .mips w := by
  by_cases h : w = 32
  · subst h
    rfl
  · rw [mips_args, ite_eq_right h]
    show _ = (if w = 32 then _ else _)
    rw [ite_eq_right h]
    rfl

theorem convention_shape (arch : Image.Arch) (w : Nat) (c : Convention)
    (h : convention arch w = some c) : Shape arch w c := by
  cases arch <;> simp only [convention, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact ⟨rfl, rfl, rfl, rfl, nil_typed, regs_typed 32 _, rfl, rfl, rfl, ra_none⟩
  · exact ⟨rfl, rfl, rfl, rfl, regs_typed 64 _, regs_typed 64 _, rfl, rfl, rfl, ra_none⟩
  · exact ⟨rfl, rfl, rfl, rfl, numbered_typed "R" 32 0 3, numbered_typed "R" 32 0 5, rfl, rfl, rfl,
      ra_some rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, numbered_typed "X" 64 0 7, numbered_typed "X" 64 0 5, rfl, rfl, rfl,
      ra_some rfl⟩
  · exact ⟨rfl, mips_names w, rfl, rfl, numbered_typed "R" w 4 _, numbered_typed "R" w 4 9, rfl, rfl,
      rfl, ra_some rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, numbered_typed "R" w 3 10, numbered_typed "R" w 3 8, rfl, rfl, rfl,
      ra_some rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, numbered_typed "X" w 10 17, numbered_typed "X" w 10 15, rfl, rfl, rfl,
      ra_some rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, numbered_typed "R" 64 2 6, numbered_typed "R" 64 2 7, rfl, rfl, rfl,
      ra_some rfl⟩

/-! ### Placement on the real conventions -/

theorem argumentNames_length (arch : Image.Arch) (w : Nat) :
    (argumentNames arch w).length = argumentRegisterCount arch w := by
  cases arch
  case mips =>
    show (if w = 32 then _ else _ : List String).length = (if w = 32 then _ else _)
    by_cases h : w = 32 <;> simp [h]
  all_goals rfl

theorem functionArguments_length (arch : Image.Arch) (w : Nat) (c : Convention)
    (h : convention arch w = some c) :
    c.functionArguments.length = argumentRegisterCount arch w := by
  have := congrArg List.length (convention_shape arch w c h).names
  rw [List.length_map, argumentNames_length] at this
  exact this

/-- Complete specification of argument placement on every supported architecture: the first
`argumentRegisterCount` arguments use the tabulated registers in order, of word type; the others
use word-spaced stack slots counted from zero. -/
theorem convention_argumentLocation (arch : Image.Arch) (w index : Nat) (c : Convention)
    (h : convention arch w = some c) :
    (∀ hi : index < argumentRegisterCount arch w, ∃ var,
        var.name = (argumentNames arch w)[index]'(by rwa [argumentNames_length]) ∧
        var.typ = .imm (expectedWordSize arch w) ∧
        argumentLocation c index = .register var) ∧
      (argumentRegisterCount arch w ≤ index → argumentLocation c index =
        .stack ((index - argumentRegisterCount arch w) * (expectedWordSize arch w / 8))) := by
  have hs := convention_shape arch w c h
  have hl := functionArguments_length arch w c h
  constructor
  · intro hi
    have hlt : index < c.functionArguments.length := by omega
    refine ⟨c.functionArguments[index], ?_, ?_, argumentLocation_of_lt c index hlt⟩
    · simp only [← hs.names]
      simp
    · rw [hs.typed.args _ (List.getElem_mem hlt), hs.word]
  · intro hge
    rw [argumentLocation_of_ge c index (by omega), hl, hs.word]

/-- With at least byte-sized words, different argument indices have different locations on every
supported architecture. -/
theorem convention_location_injective (arch : Image.Arch) (w : Nat) (c : Convention)
    (h : convention arch w = some c) (hw : 8 ≤ w) (i j : Nat)
    (he : argumentLocation c i = argumentLocation c j) : i = j := by
  have hs := convention_shape arch w c h
  have hf := convention_registerFacts arch w c h
  have hnodup : c.functionArguments.Nodup := by
    have := hf.argsNodup
    refine List.Pairwise.imp_of_mem ?_ (List.pairwise_map.1 this)
    intro a b _ _ hne hab
    exact hne (congrArg _ hab)
  refine argumentLocation_injective c hnodup ?_ i j he
  rw [hs.word]
  cases arch <;> first | exact hw | exact (by decide : 8 ≤ 64) | exact (by decide : 8 ≤ 32)

/-- Registers holding function arguments never include the stack pointer, so placing an argument
in a register cannot clobber the stack. -/
theorem register_argument_not_stackPointer (arch : Image.Arch) (w index : Nat) (c : Convention)
    (h : convention arch w = some c) (var : Bap.Var)
    (hl : argumentLocation c index = .register var) : var.name ≠ c.stackPointer.name := by
  have hf := convention_registerFacts arch w c h
  intro he
  exact hf.spNotArg (he ▸ List.mem_map.2 ⟨var, argumentLocation_register_mem c index var hl, rfl⟩)

/-- On the RISC, ARM and SystemZ conventions the result register doubles as the first argument. -/
theorem result_is_first_argument (arch : Image.Arch) (w : Nat) (c : Convention)
    (h : convention arch w = some c)
    (ha : arch = .riscv ∨ arch = .aarch64 ∨ arch = .arm ∨ arch = .powerpc ∨ arch = .systemz) :
    c.functionArguments.head? = some c.result := by
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    simp only [convention, Option.some.injEq] at h <;> subst h <;> rfl

/-! ### Word sizes that follow the target -/

/-- MIPS passes eight arguments in registers from `R4` under n32 and n64, four under o32. -/
theorem mips_argument_registers (w : Nat) (c : Convention) (h : convention .mips w = some c) :
    c.functionArguments.length = if w = 32 then 4 else 8 :=
  functionArguments_length .mips w c h

/-- Intended, as in `plugins/mips/mips_abi.ml`, where the memory arguments are allocated from the
stack pointer: the convention doesn't model the 16-byte home area of the o32 psABI, so the first
stack argument is at offset 0 for the 32-bit and the 64-bit MIPS. -/
theorem mips_first_stack_argument (w : Nat) (c : Convention) (h : convention .mips w = some c) :
    argumentLocation c (if w = 32 then 4 else 8) = .stack 0 := by
  have hl := mips_argument_registers w c h
  rw [← hl]
  exact first_stack_argument c

/-- x86 is a 32-bit target, whatever word size is asked of it, including the default: registers
are 32 bits wide and the arguments, all on the stack, take four bytes each. -/
theorem x86_is_32_bit (w index : Nat) (c : Convention) (h : convention .x86 w = some c) :
    c.wordSize = 32 ∧ c.result.typ = .imm 32 ∧ c.stackPointer.typ = .imm 32 ∧
      argumentLocation c index = .stack (index * 4) := by
  simp only [convention, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, by
    rw [argumentLocation_of_ge _ _ (Nat.zero_le index)]
    show Location.stack ((index - 0) * (32 / 8)) = _
    simp⟩

end Bap.Proofs.ABI
