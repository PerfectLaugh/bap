import Lean.Elab.Command
import Bap.Symbolic.Executor
import Bap.Bil.Typecheck

namespace Bap.Proofs.Symbolic

open Lean Elab Command in
/-- Bind short names to private declarations of an imported module (`open private` lives in Batteries). -/
local elab "open_private_decls " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

open Bap.Symbolic
open_private_decls Bap.Symbolic.Memory Bap.Symbolic.Memory offsetAddress byteAt
open_private_decls Bap.Symbolic.Executor Bap.Symbolic lookup binaryApp signedDivision binary evalCast
  isMemoryType evalMemory freshen withConstraint expectCondition
  executeStmt executeProgram executeStmt.continueResults executeProgram.continueResults

/-! ### Expressions -/

@[simp] theorem width_bool (value : Bool) : (Expr.bool value).width = 1 := rfl

/-- Path-condition builders always produce a one-bit expression on one-bit input. -/
theorem width_eqOne (value : Expr) (h : value.width = 1) : (Expr.eqOne value).width = 1 := by
  simp [Expr.eqOne, h]

@[simp] theorem width_eqZero (value : Expr) : (Expr.eqZero value).width = 1 := rfl

theorem eqOne_of_width_one {value : Expr} (h : value.width = 1) : Expr.eqOne value = value := by
  simp [Expr.eqOne, h]

theorem width_extract_of_le {high low : Nat} (value : Expr) (h : low ≤ high) :
    (Expr.extract high low value).width + low = high + 1 := by
  simp only [Expr.width]; omega

/-- An inverted `extract` denotes no bits; the executor rejects it. -/
theorem width_extract_inverted {high low : Nat} (value : Expr) (h : high < low) :
    (Expr.extract high low value).width = 0 := by
  simp only [Expr.width]; omega

/-- Structural equality is equality of expressions, which makes it a decision procedure. -/
theorem structuralEq_iff {left right : Expr} : Expr.structuralEq left right = true ↔ left = right :=
  Expr.eq_of_structuralEq

theorem structuralEq_false_iff {left right : Expr} : Expr.structuralEq left right = false ↔ left ≠ right := by
  have := @structuralEq_iff left right
  cases h : Expr.structuralEq left right <;> simp_all

@[simp] theorem structuralEq_refl (e : Expr) : Expr.structuralEq e e = true := structuralEq_iff.mpr rfl

theorem structuralEq_symm (left right : Expr) :
    Expr.structuralEq left right = Expr.structuralEq right left := by
  cases h : Expr.structuralEq right left with
  | true => rw [structuralEq_iff.mp h]; simp
  | false =>
    rw [structuralEq_false_iff] at h ⊢
    exact fun e => h e.symm

theorem structuralEq_trans {a b c : Expr} (hab : Expr.structuralEq a b = true)
    (hbc : Expr.structuralEq b c = true) : Expr.structuralEq a c = true := by
  rw [structuralEq_iff] at *
  exact hab.trans hbc

/-- Variables are equal exactly when both name and width are. -/
theorem structuralEq_var (name name' : String) (width width' : Nat) :
    Expr.structuralEq (.var name width) (.var name' width') = true ↔ name = name' ∧ width = width' := by
  simp [structuralEq_iff]

theorem structuralEq_const_iff {w : Nat} (a b : BitVec w) :
    Expr.structuralEq (.const a) (.const b) = true ↔ a = b := by
  simp [structuralEq_iff]

theorem mem_vars_concat {v : String × Nat} {left right : Expr} :
    v ∈ (Expr.concat left right).vars ↔ v ∈ left.vars ∨ v ∈ right.vars := by
  rw [Expr.vars]; simp [List.mem_eraseDups]

theorem mem_vars_ite {v : String × Nat} {c yes no : Expr} :
    v ∈ (Expr.ite c yes no).vars ↔ v ∈ c.vars ∨ v ∈ yes.vars ∨ v ∈ no.vars := by
  rw [Expr.vars]; simp [List.mem_eraseDups]

theorem mem_vars_app {v : String × Nat} {name : String} {width : Nat} {args : List Expr} :
    v ∈ (Expr.app name width args).vars ↔ ∃ arg ∈ args, v ∈ arg.vars := by
  rw [Expr.vars]; simp [List.mem_eraseDups]

/-! ### Denotation

The meaning of an expression under an assignment of its inputs. Each operator means what SMT-LIB says:
`Word.udiv`, `Word.urem` and `Word.srem` have SMT-LIB's zero-divisor behaviour, see `word_udiv_smt` and so
on below. -/

/-- Values for the inputs: the variables, and the initial contents of the memories. -/
structure Assignment where
  var : String → (width : Nat) → BitVec width
  memory : String → (addressWidth : Nat) → BitVec addressWidth → BitVec 8

abbrev Bits := Σ width, BitVec width

def isOne (value : Bits) : Bool := value.2.toNat == 1

def sameBits (left right : Bits) : Bool := left.1 == right.1 && left.2.toNat == right.2.toNat

theorem bits_ext {a b : Bits} (h1 : a.1 = b.1) (h2 : a.2.toNat = b.2.toNat) : a = b := by
  obtain ⟨w, x⟩ := a
  obtain ⟨v, y⟩ := b
  simp only at h1 h2
  subst h1
  cases BitVec.eq_of_toNat_eq h2
  rfl

theorem sameBits_iff {a b : Bits} : sameBits a b = true ↔ a = b := by
  constructor
  · intro h
    simp only [sameBits, Bool.and_eq_true, beq_iff_eq] at h
    exact bits_ext h.1 h.2
  · rintro rfl
    simp [sameBits]

def wordOp (name : String) {w : Nat} (x y : BitVec w) : Bits :=
  if name = "bvadd" then ⟨w, x + y⟩
  else if name = "bvsub" then ⟨w, x - y⟩
  else if name = "bvmul" then ⟨w, x * y⟩
  else if name = "bvudiv" then ⟨w, Word.udiv x y⟩
  else if name = "bvsdiv" then ⟨w, BitVec.smtSDiv x y⟩
  else if name = "bvurem" then ⟨w, Word.urem x y⟩
  else if name = "bvsrem" then ⟨w, Word.srem x y⟩
  else if name = "bvsmod" then ⟨w, BitVec.smod x y⟩
  else if name = "bvshl" then ⟨w, Word.shl x y⟩
  else if name = "bvlshr" then ⟨w, Word.lshr x y⟩
  else if name = "bvashr" then ⟨w, Word.ashr x y⟩
  else if name = "bvand" then ⟨w, x &&& y⟩
  else if name = "bvor" then ⟨w, x ||| y⟩
  else if name = "bvxor" then ⟨w, x ^^^ y⟩
  else if name = "=" then ⟨1, Word.eq x y⟩
  else if name = "distinct" then ⟨1, Word.neq x y⟩
  else if name = "bvult" then ⟨1, Word.lt x y⟩
  else if name = "bvule" then ⟨1, Word.le x y⟩
  else if name = "bvugt" then ⟨1, Word.lt y x⟩
  else if name = "bvuge" then ⟨1, Word.le y x⟩
  else if name = "bvslt" then ⟨1, Word.slt x y⟩
  else if name = "bvsle" then ⟨1, Word.sle x y⟩
  else if name = "bvsgt" then ⟨1, Word.slt y x⟩
  else if name = "bvsge" then ⟨1, Word.sle y x⟩
  else ⟨w, 0⟩

def denoteBinary (name : String) (left right : Bits) : Bits :=
  if h : right.1 = left.1 then wordOp name left.2 (h ▸ right.2)
  else if Expr.isPredicate name then ⟨1, 0⟩ else ⟨left.1, 0⟩

def denoteUnary (name : String) (width : Nat) (value : Bits) : Bits :=
  if name = "bvneg" then ⟨value.1, -value.2⟩
  else if name = "bvnot" then ⟨value.1, ~~~value.2⟩
  else if name = s!"(_ {"sign_extend"} {width - value.1})" then ⟨width, BitVec.signExtend width value.2⟩
  else if name = s!"(_ {"zero_extend"} {width - value.1})" then ⟨width, BitVec.zeroExtend width value.2⟩
  else ⟨width, 0⟩

def denote (σ : Assignment) : Expr → Bits
  | .var name width => ⟨width, σ.var name width⟩
  | .const value => ⟨_, value⟩
  | .app name width [value] => denoteUnary name width (denote σ value)
  | .app name _ [left, right] => denoteBinary name (denote σ left) (denote σ right)
  | .app _ width _ => ⟨width, 0⟩
  | .extract high low value => ⟨_, BitVec.extractLsb high low (denote σ value).2⟩
  | .concat left right => ⟨_, BitVec.append (denote σ left).2 (denote σ right).2⟩
  | .ite condition yes no => if isOne (denote σ condition) then denote σ yes else denote σ no
  | .select memory address => ⟨8, σ.memory memory _ (denote σ address).2⟩

/-- An expression holds when it denotes one, which is what an assertion of it says in SMT-LIB. -/
def Holds (σ : Assignment) (e : Expr) : Prop := isOne (denote σ e) = true

theorem word_udiv_smt {w : Nat} (x y : BitVec w) : Word.udiv x y = BitVec.smtUDiv x y := rfl

theorem word_urem_smt {w : Nat} (x y : BitVec w) : Word.urem x y = x % y := by
  unfold Word.urem
  split
  · next h => subst h; simp
  · rfl

theorem word_srem_smt {w : Nat} (x y : BitVec w) : Word.srem x y = BitVec.srem x y := by
  unfold Word.srem
  split
  · next h => subst h; simp
  · rfl

/-- BIL's signed division agrees with SMT-LIB's except for a zero divisor. -/
theorem word_sdiv_smt {w : Nat} (x y : BitVec w) (h : y ≠ 0) : Word.sdiv x y = BitVec.smtSDiv x y := by
  have hn : y.neg ≠ 0 := fun e => h (by simpa using (BitVec.neg_eq_zero_iff (x := y)).mp e)
  simp only [Word.sdiv, h, ↓reduceIte, BitVec.sdiv, BitVec.smtSDiv, BitVec.smtUDiv, hn]

/-- ...which is why the executor emits a guard. Here `-1 /$ 0` is `-1` in BIL, and `1` in SMT-LIB. -/
theorem word_sdiv_zero_differs : Word.sdiv (BitVec.allOnes 8) 0#8 ≠ BitVec.smtSDiv (BitVec.allOnes 8) 0#8 := by
  decide

@[simp] theorem denote_var (σ : Assignment) (name : String) (w : Nat) :
    denote σ (.var name w) = ⟨w, σ.var name w⟩ := by simp [denote]

@[simp] theorem denote_const (σ : Assignment) {w : Nat} (x : BitVec w) :
    denote σ (.const x) = ⟨w, x⟩ := by simp [denote]

theorem denote_binary (σ : Assignment) (name : String) (width : Nat) (left right : Expr) :
    denote σ (.app name width [left, right]) = denoteBinary name (denote σ left) (denote σ right) := by
  simp [denote]

theorem denote_ite (σ : Assignment) (c y n : Expr) :
    denote σ (.ite c y n) = if isOne (denote σ c) then denote σ y else denote σ n := by
  simp [denote]

theorem isOne_bit (b : Bool) : isOne ⟨1, Word.bool b⟩ = b := by
  cases b <;> rfl

/-- An equality guard holds exactly when both sides denote the same bits. -/
theorem isOne_denote_eq (σ : Assignment) (w : Nat) (left right : Expr) :
    isOne (denote σ (.app "=" w [left, right])) = sameBits (denote σ left) (denote σ right) := by
  rw [denote_binary]
  obtain ⟨u, x⟩ := denote σ left
  obtain ⟨v, y⟩ := denote σ right
  simp only [denoteBinary, sameBits]
  by_cases h : v = u
  · subst h
    simp only [dite_true, wordOp, isOne_bit, Word.eq, reduceIte, String.reduceEq]
    simp only [beq_self_eq_true, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp [BitVec.toNat_eq]
  · have h' : ¬ u = v := fun e => h e.symm
    have hp : Expr.isPredicate "=" = true := by decide
    rw [dite_eq_right_of_eq_false (eq_false h)]
    simp [hp, isOne, h']

/-! ### The byte map a memory denotes -/

def byteOf (σ : Assignment) (value : Expr) : BitVec 8 := BitVec.ofNat 8 (denote σ value).2.toNat

theorem denote_of_width8 {σ : Assignment} {value : Expr} (h : (denote σ value).1 = 8) :
    denote σ value = ⟨8, byteOf σ value⟩ := by
  unfold byteOf
  generalize denote σ value = b at h ⊢
  obtain ⟨w, x⟩ := b
  simp only at h
  subst h
  simp

/-- The concrete bytes of a list of writes over the initial contents of a memory. -/
def byteMap (σ : Assignment) (name : String) : List (Expr × Expr) → Bits → BitVec 8
  | [], target => σ.memory name target.1 target.2
  | cell :: rest, target =>
    if sameBits (denote σ cell.1) target then byteOf σ cell.2 else byteMap σ name rest target

def CellsSized (σ : Assignment) (cells : List (Expr × Expr)) : Prop :=
  ∀ cell ∈ cells, (denote σ cell.2).1 = 8 ∧ cell.2.width = 8

theorem definitelyDistinct_sound (σ : Assignment) {a b : Expr} (h : Memory.definitelyDistinct a b = true) :
    sameBits (denote σ a) (denote σ b) = false := by
  cases a <;> cases b <;> simp only [Memory.definitelyDistinct, reduceCtorEq] at h
  rw [denote_const, denote_const]
  simp at h
  simp only [sameBits, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  exact h

/-- Soundness under aliasing: for any assignment, a symbolic read denotes the byte the writes leave at
the location its address denotes. -/
theorem denote_readCells (σ : Assignment) (name : String) (address : Expr) (cells : List (Expr × Expr))
    (h : CellsSized σ cells) :
    denote σ (Memory.readCells name address cells) = ⟨8, byteMap σ name cells (denote σ address)⟩ := by
  induction cells with
  | nil => simp [Memory.readCells, byteMap, denote]
  | cons cell rest ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hcell := denote_of_width8 (h cell (by simp)).1
    simp only [Memory.readCells, byteMap]
    cases hs : Expr.structuralEq cell.1 address with
    | true =>
      have he := structuralEq_iff.mp hs
      have : sameBits (denote σ cell.1) (denote σ address) = true := sameBits_iff.mpr (by rw [he])
      simp only [this, ↓reduceIte, hcell]
    | false =>
      cases hd : Memory.definitelyDistinct cell.1 address with
      | true =>
        have := definitelyDistinct_sound σ hd
        simp only [this, ↓reduceIte, Bool.false_eq_true, ih']
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, denote_ite, isOne_denote_eq]
        cases hm : sameBits (denote σ cell.1) (denote σ address) with
        | true => simp only [↓reduceIte, hcell]
        | false => simp only [↓reduceIte, Bool.false_eq_true, ih']

theorem denote_readByte (σ : Assignment) (memory : Bap.Symbolic.Memory) (address : Expr)
    (h : CellsSized σ memory.cells) :
    denote σ (memory.readByte address) = ⟨8, byteMap σ memory.name memory.cells (denote σ address)⟩ :=
  denote_readCells σ _ _ _ h

/-- A byte write updates the byte map at the one location its address denotes. -/
theorem byteMap_writeByte (σ : Assignment) (memory : Bap.Symbolic.Memory) (address value : Expr) (target : Bits) :
    byteMap σ memory.name (memory.writeByte address value).cells target =
      if sameBits (denote σ address) target then byteOf σ value
      else byteMap σ memory.name memory.cells target := by
  simp only [Bap.Symbolic.Memory.writeByte, byteMap]
  split
  · rfl
  · next hne =>
    generalize memory.cells = cells
    induction cells with
    | nil => rfl
    | cons cell rest ih =>
      by_cases hc : Expr.structuralEq cell.1 address = true
      · have he := structuralEq_iff.mp hc
        have hsb : sameBits (denote σ cell.1) target = false := by
          rw [he]; exact Bool.eq_false_iff.mpr hne
        simp only [List.filter_cons, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, byteMap, hsb, ih]
      · simp only [List.filter_cons, hc, Bool.not_false, ↓reduceIte, byteMap, ih]

theorem cellsSized_writeByte {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : CellsSized σ memory.cells)
    (address : Expr) {value : Expr} (hv : (denote σ value).1 = 8) (hw : value.width = 8) :
    CellsSized σ (memory.writeByte address value).cells := by
  intro cell hcell
  rcases List.mem_cons.mp hcell with rfl | hcell
  · exact ⟨hv, hw⟩
  · exact h cell (List.mem_filter.mp hcell).1

/-- The cell addresses stay pairwise distinct, so a write can't be shadowed by a stale equal address. -/
theorem writeByte_keys_distinct (memory : Bap.Symbolic.Memory) (address value : Expr)
    (h : memory.cells.Pairwise fun x y => x.1 ≠ y.1) :
    (memory.writeByte address value).cells.Pairwise fun x y => x.1 ≠ y.1 := by
  simp only [Bap.Symbolic.Memory.writeByte]
  refine List.pairwise_cons.mpr ⟨?_, h.filter _⟩
  intro cell hcell
  have := (List.mem_filter.mp hcell).2
  simp only [Bool.not_eq_true', structuralEq_false_iff] at this
  exact fun e => this e.symm

theorem writeByte_writeByte_same (memory : Bap.Symbolic.Memory) (address first second : Expr) :
    (memory.writeByte address first).writeByte address second = memory.writeByte address second := by
  simp [Bap.Symbolic.Memory.writeByte, List.filter_filter]

/-! ### Multi-byte accesses against a concrete byte map -/

/-- A concrete memory: the byte at each location. -/
abbrev ByteMap := Bits → BitVec 8

def offsetBits (target : Bits) (offset : Nat) : Bits :=
  ⟨target.1, target.2 + BitVec.ofNat target.1 offset⟩

def valueByte (value : Bits) (index : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (value.2.toNat >>> (index * 8))

/-- The bytes of a concrete write. -/
def modelWrite (bytes : ByteMap) (target value : Bits) (endian : Endian) (size : Nat) : ByteMap :=
  (List.range size).foldl (init := bytes) fun bytes offset location =>
    if sameBits (offsetBits target offset) location then
      valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
    else bytes location

/-- The value of a concrete read, assembled just as `Bap.Memory.read` does. -/
def modelRead (bytes : ByteMap) (target : Bits) (endian : Endian) (size : Nat) : Nat :=
  let read := (List.range size).map fun offset => bytes (offsetBits target offset)
  let ordered := match endian with
    | .little => read.reverse
    | .big => read
  ordered.foldl (fun result byte => result * 256 + byte.toNat) 0

theorem denote_offsetAddress (σ : Assignment) (address : Expr) (offset : Nat)
    (h : (denote σ address).1 = address.width) :
    denote σ (offsetAddress address offset) = offsetBits (denote σ address) offset := by
  unfold offsetAddress
  split
  · rw [denote_const, denote_const]; rfl
  · split
    · next h0 =>
      subst h0
      exact bits_ext (b := offsetBits _ 0) rfl (by simp [offsetBits])
    · rw [denote_binary, denote_const]
      generalize denote σ address = d at h ⊢
      obtain ⟨w, x⟩ := d
      simp only at h
      rw [← h]
      simp [denoteBinary, wordOp, offsetBits]

theorem byteOf_byteAt (σ : Assignment) (value : Expr) (index : Nat) :
    byteOf σ (byteAt value index) = valueByte (denote σ value) index := by
  simp only [byteOf, byteAt, valueByte, denote, BitVec.extractLsb_toNat]
  have hw : index * 8 + 7 - index * 8 + 1 = 8 := by omega
  rw [hw]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]

theorem width_denote_byteAt (σ : Assignment) (value : Expr) (index : Nat) :
    (denote σ (byteAt value index)).1 = 8 := by
  simp only [byteAt, denote]; omega

private def writeStep (address value : Expr) (endian : Endian) (size : Nat)
    (memory : Bap.Symbolic.Memory) (offset : Nat) : Bap.Symbolic.Memory :=
  memory.writeByte (offsetAddress address offset)
    (byteAt value (if endian = Bap.Endian.little then offset else size - 1 - offset))

private def writePrefix (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian) (size k : Nat) :
    Bap.Symbolic.Memory :=
  (List.range k).foldl (writeStep address value endian size) memory

private theorem write_eq_prefix (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian) (size : Nat) :
    memory.write address value endian size = writePrefix memory address value endian size size := rfl

private theorem writePrefix_succ (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian) (size k : Nat) :
    writePrefix memory address value endian size (k + 1) =
      writeStep address value endian size (writePrefix memory address value endian size k) k := by
  simp [writePrefix, List.range_succ, List.foldl_append]

private theorem name_writePrefix (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian) (size k : Nat) :
    (writePrefix memory address value endian size k).name = memory.name := by
  induction k with
  | zero => rfl
  | succ k ih => rw [writePrefix_succ]; exact ih

theorem name_write (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian) (size : Nat) :
    (memory.write address value endian size).name = memory.name :=
  name_writePrefix ..

theorem cellsSized_write {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : CellsSized σ memory.cells)
    (address value : Expr) (endian : Endian) (size : Nat) :
    CellsSized σ (memory.write address value endian size).cells := by
  rw [write_eq_prefix]
  have : ∀ k, CellsSized σ (writePrefix memory address value endian size k).cells := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [writePrefix_succ]
      exact cellsSized_writeByte ih _ (width_denote_byteAt ..) (by simp only [byteAt, Expr.width]; omega)
  exact this size

private theorem modelWrite_succ (bytes : ByteMap) (target value : Bits) (endian : Endian) (size k : Nat) :
    (List.range (k + 1)).foldl (init := bytes) (fun bytes offset location =>
      if sameBits (offsetBits target offset) location then
        valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
      else bytes location) = fun location =>
        if sameBits (offsetBits target k) location then
          valueByte value (match endian with | .little => k | .big => size - 1 - k)
        else (List.range k).foldl (init := bytes) (fun bytes offset location =>
          if sameBits (offsetBits target offset) location then
            valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
          else bytes location) location := by
  simp [List.range_succ, List.foldl_append]

/-- A multi-byte write updates the byte map exactly as the concrete write does, for any assignment. -/
theorem byteMap_write (σ : Assignment) (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian)
    (size : Nat) (h : (denote σ address).1 = address.width) (target : Bits) :
    byteMap σ memory.name (memory.write address value endian size).cells target =
      modelWrite (byteMap σ memory.name memory.cells) (denote σ address) (denote σ value) endian size target := by
  rw [write_eq_prefix]
  have : ∀ k target, byteMap σ memory.name (writePrefix memory address value endian size k).cells target =
      (List.range k).foldl (init := byteMap σ memory.name memory.cells) (fun bytes offset location =>
        if sameBits (offsetBits (denote σ address) offset) location then
          valueByte (denote σ value) (match endian with | .little => offset | .big => size - 1 - offset)
        else bytes location) target := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro target
      rw [modelWrite_succ, writePrefix_succ]
      simp only
      have hname := name_writePrefix memory address value endian size k
      have := byteMap_writeByte σ (writePrefix memory address value endian size k)
        (offsetAddress address k)
        (byteAt value (if endian = Bap.Endian.little then k else size - 1 - k)) target
      rw [hname] at this
      rw [writeStep, this, denote_offsetAddress σ address k h, byteOf_byteAt, ih]
      cases endian <;> rfl
  exact this size target

private theorem toNat_lt_of_width {b : Bits} {n : Nat} (h : b.1 = n) : b.2.toNat < 2 ^ n := by
  obtain ⟨w, x⟩ := b
  simp only at h
  subst h
  exact x.isLt

/-- The bytes of a read, most significant first, as a chain of concatenations. -/
def chainBytes : List Expr → Expr
  | [] => .const (BitVec.zero 0)
  | first :: rest => rest.foldl (fun result byte => .concat result byte) first

private theorem byteOf_of_eq {σ : Assignment} {value : Expr} {b : BitVec 8} (h : denote σ value = ⟨8, b⟩) :
    byteOf σ value = b := by
  unfold byteOf
  rw [h]
  simp

private theorem chain_denote (σ : Assignment) (rest : List Expr) (first : Expr)
    (h : ∀ b ∈ rest, (denote σ b).1 = 8) :
    (denote σ (rest.foldl (fun result byte => .concat result byte) first)).1 =
        (denote σ first).1 + 8 * rest.length ∧
      (denote σ (rest.foldl (fun result byte => .concat result byte) first)).2.toNat =
        (rest.map (byteOf σ)).foldl (fun result byte => result * 256 + byte.toNat) (denote σ first).2.toNat := by
  induction rest generalizing first with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨h1, h2⟩ := ih (.concat first b) fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hb := h b (by simp)
    simp only [List.foldl_cons, List.map_cons, List.length_cons]
    refine ⟨?_, ?_⟩
    · rw [h1]
      have : (denote σ (first.concat b)).1 = (denote σ first).1 + (denote σ b).1 := rfl
      rw [this, hb]
      omega
    · rw [h2]
      congr 1
      have hc : (denote σ (first.concat b)).2.toNat =
          (denote σ first).2.toNat <<< (denote σ b).1 ||| (denote σ b).2.toNat := by
        show (BitVec.append (denote σ first).2 (denote σ b).2).toNat = _
        exact BitVec.toNat_append ..
      have hs : (denote σ first).2.toNat <<< (denote σ b).1 = (denote σ first).2.toNat <<< 8 := by rw [hb]
      rw [hc, hs]
      have hlt := toNat_lt_of_width hb
      have hbyte : (byteOf σ b).toNat = (denote σ b).2.toNat := by
        simp [byteOf, Nat.mod_eq_of_lt hlt]
      rw [hbyte, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]

/-- Soundness of multi-byte reads under aliasing, for any assignment: the expression denotes the value
that a concrete read of the byte map would produce, with the width the type checker promises. -/
theorem denote_read (σ : Assignment) (memory : Bap.Symbolic.Memory) (address : Expr) (endian : Endian) (size : Nat)
    (hcells : CellsSized σ memory.cells) (h : (denote σ address).1 = address.width) :
    (denote σ (memory.read address endian size)).1 = size * 8 ∧
      (denote σ (memory.read address endian size)).2.toNat =
        modelRead (byteMap σ memory.name memory.cells) (denote σ address) endian size := by
  have hbyte : ∀ offset, denote σ (memory.readByte (offsetAddress address offset)) =
      ⟨8, byteMap σ memory.name memory.cells (offsetBits (denote σ address) offset)⟩ := by
    intro offset
    rw [denote_readByte σ memory _ hcells, denote_offsetAddress σ address offset h]
  let exprs := (List.range size).map fun offset => memory.readByte (offsetAddress address offset)
  have hbytes : exprs.map (byteOf σ) =
      (List.range size).map fun offset =>
        byteMap σ memory.name memory.cells (offsetBits (denote σ address) offset) := by
    simp only [exprs, List.map_map]
    apply List.map_congr_left
    intro offset _
    exact byteOf_of_eq (hbyte offset)
  have hordered : ∀ ordered : List Expr, (∀ b ∈ ordered, (denote σ b).1 = 8) → ordered.length = size →
      (denote σ (chainBytes ordered)).1 = size * 8 ∧
      (denote σ (chainBytes ordered)).2.toNat =
        (ordered.map (byteOf σ)).foldl (fun result byte => result * 256 + byte.toNat) 0 := by
    intro ordered hw hl
    cases ordered with
    | nil =>
      simp at hl
      subst hl
      simp [chainBytes, denote]
    | cons first rest =>
      have hf := hw first (by simp)
      obtain ⟨h1, h2⟩ := chain_denote σ rest first fun x hx => hw x (List.mem_cons_of_mem _ hx)
      refine ⟨?_, ?_⟩
      · simp only [chainBytes]
        rw [h1, hf]
        simp at hl
        omega
      · simp only [chainBytes, List.map_cons, List.foldl_cons]
        rw [h2]
        congr 1
        have := toNat_lt_of_width hf
        simp [byteOf, Nat.mod_eq_of_lt this]
  have hw : ∀ b ∈ exprs, (denote σ b).1 = 8 := by
    intro b hb
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp hb
    rw [hbyte]
  have hlen : exprs.length = size := by simp [exprs]
  have hread : memory.read address endian size =
      chainBytes (match endian with | .little => exprs.reverse | .big => exprs) := by
    unfold Bap.Symbolic.Memory.read
    cases endian
    · simp only [↓reduceIte, exprs]
      generalize (List.map _ (List.range size)).reverse = l
      cases l <;> rfl
    · simp only [↓reduceIte, reduceCtorEq, exprs]
      generalize List.map _ (List.range size) = l
      cases l <;> rfl
  rw [hread]
  simp only [modelRead]
  cases endian with
  | little =>
    have := hordered exprs.reverse (by simpa using hw) (by simpa using hlen)
    simpa only [List.map_reverse, hbytes] using this
  | big =>
    have := hordered exprs hw hlen
    simpa only [hbytes] using this

/-! ### Expression soundness against the BIL evaluator -/

open_private_decls Bap.Bil.Eval Bap.Bil expectMemory evalUn

/-- A symbolic memory stands for a concrete one when the bytes agree at every location. -/
def MemRel (σ : Assignment) (memory : Bap.Symbolic.Memory) {w : Nat} (concrete : Bap.Memory w) : Prop :=
  ∀ address : BitVec w, (Bap.Memory.readByte concrete address).toBitVec =
    byteMap σ memory.name memory.cells ⟨w, address⟩

/-- The expressions and memories of a state are sized as their `width`s claim. -/
structure WellSized (σ : Assignment) (s : State) : Prop where
  envSized : ∀ entry ∈ s.env, (denote σ entry.2).1 = entry.2.width
  cellsSized : ∀ entry ∈ s.memories, CellsSized σ entry.2.cells

/-- A symbolic state stands for a concrete environment under an assignment. -/
structure Rel (σ : Assignment) (s : State) (env : Bil.Env) : Prop extends WellSized σ s where
  vars : ∀ var x w (v : BitVec w), isMemoryType var.typ = false → Assoc.get var s.env = some x →
    Bil.lookup env var = .ok (.bits v) → denote σ x = ⟨w, v⟩
  mems : ∀ var w (concrete : Bap.Memory w), isMemoryType var.typ = true →
    Bil.lookup env var = .ok (.memory concrete) → MemRel σ (memoryOf s var) concrete

private theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

private theorem get_mem {α β : Type} [DecidableEq α] {l : List (α × β)} {k : α} {x : β}
    (h : Assoc.get k l = some x) : (k, x) ∈ l := by
  induction l with
  | nil => simp [Assoc.get] at h
  | cons entry rest ih =>
    obtain ⟨a, b⟩ := entry
    by_cases hk : k = a
    · subst hk
      simp [Assoc.get] at h
      simp [h]
    · have hb : (k == a) = false := by simpa using hk
      exact List.mem_cons_of_mem _ (ih (by simpa [Assoc.get, List.lookup, hb] using h))

private theorem lookup_ok {env : Env} {var : Bap.Var} {x : Expr} (h : lookup env var = .ok x) :
    isMemoryType var.typ = false ∧ Assoc.get var env = some x := by
  unfold lookup at h
  cases ht : var.typ <;> simp only [isMemoryType, true_and] <;> simp only [ht] at h
  case mem => cases h
  all_goals
    simp only [↓reduceIte, Bool.false_eq_true] at h
    split at h
    · next heq => cases h; exact heq
    · cases h

theorem cells_memoryOf {σ : Assignment} {s : State} (h : WellSized σ s) (var : Bap.Var) :
    CellsSized σ (memoryOf s var).cells := by
  unfold memoryOf
  split
  · next memory heq => exact h.cellsSized _ (get_mem heq)
  · intro _ hc; cases hc

def symbolicBinary (op : Bil.BinOp) (left right : Expr) : Expr :=
  match op with
  | .sdiv => signedDivision left right
  | _ => binaryApp op left right

private theorem binary_cases (op : Bil.BinOp) (left right : Expr) :
    binary op left right = symbolicBinary op left right ∨
      ∃ (lw : Nat) (lv : BitVec lw) (rw : Nat) (rv : BitVec rw) (w : Nat) (v : BitVec w),
        left = .const lv ∧ right = .const rv ∧ Bil.evalBin op ⟨lw, lv⟩ ⟨rw, rv⟩ = .ok (.bits v) ∧
        binary op left right = .const v := by
  cases left <;> cases right <;> first | (left; cases op <;> rfl) | skip
  next lw lv rw rv =>
    cases h : Bil.evalBin op ⟨lw, lv⟩ ⟨rw, rv⟩ with
    | error e => exact .inl (by cases op <;> simp_all [binary] <;> rfl)
    | ok value =>
      cases value with
      | bits v => exact .inr ⟨lw, lv, rw, rv, _, v, rfl, rfl, h, by simp [binary, h]⟩
      | memory m => exact .inl (by cases op <;> simp_all [binary] <;> rfl)
      | undefined => exact .inl (by cases op <;> simp_all [binary] <;> rfl)

def bilBinary (op : Bil.BinOp) {w : Nat} (x y : BitVec w) : Bits :=
  match op with
  | .add => ⟨_, x + y⟩
  | .sub => ⟨_, x - y⟩
  | .mul => ⟨_, x * y⟩
  | .div => ⟨_, Word.udiv x y⟩
  | .sdiv => ⟨_, Word.sdiv x y⟩
  | .rem => ⟨_, Word.urem x y⟩
  | .srem => ⟨_, Word.srem x y⟩
  | .smod => ⟨_, Word.smod x y⟩
  | .lshift => ⟨_, Word.shl x y⟩
  | .rshift => ⟨_, Word.lshr x y⟩
  | .ashift => ⟨_, Word.ashr x y⟩
  | .and => ⟨_, x &&& y⟩
  | .or => ⟨_, x ||| y⟩
  | .xor => ⟨_, x ^^^ y⟩
  | .eq => ⟨_, Word.eq x y⟩
  | .neq => ⟨_, Word.neq x y⟩
  | .lt => ⟨_, Word.lt x y⟩
  | .le => ⟨_, Word.le x y⟩
  | .gt => ⟨_, Word.lt y x⟩
  | .ge => ⟨_, Word.le y x⟩
  | .slt => ⟨_, Word.slt x y⟩
  | .sle => ⟨_, Word.sle x y⟩
  | .sgt => ⟨_, Word.slt y x⟩
  | .sge => ⟨_, Word.sle y x⟩

private theorem evalBin_same (op : Bil.BinOp) {w : Nat} (x y : BitVec w) :
    ∃ v : BitVec (bilBinary op x y).1, Bil.evalBin op ⟨w, x⟩ ⟨w, y⟩ = .ok (.bits v) ∧
      (⟨_, v⟩ : Bits) = bilBinary op x y := by
  cases op <;> exact ⟨_, by simp [Bil.evalBin, bilBinary]; try rfl, rfl⟩

private theorem wordOp_app {σ : Assignment} {left right : Expr} {w : Nat} {x y : BitVec w}
    (hl : denote σ left = ⟨w, x⟩) (hr : denote σ right = ⟨w, y⟩) (name : String) (k : Nat) :
    denote σ (.app name k [left, right]) = wordOp name x y := by
  rw [denote_binary, hl, hr]
  simp [denoteBinary]

private theorem isOne_bit_true : isOne ⟨1, 1#1⟩ = true := rfl

private theorem const_zero_of_width {e : Expr} {w : Nat} (h : e.width = w) :
    Expr.const (BitVec.ofNat e.width 0) = Expr.const (BitVec.ofNat w 0) := by rw [h]

private theorem const_ones_of_width {e : Expr} {w : Nat} (h : e.width = w) :
    Expr.const (BitVec.allOnes e.width) = Expr.const (BitVec.allOnes w) := by rw [h]

/-- The expression built for a binary operator denotes BIL's value of that operator. -/
theorem denote_symbolicBinary {σ : Assignment} (op : Bil.BinOp) {left right : Expr} {w : Nat} {x y : BitVec w}
    (hl : denote σ left = ⟨w, x⟩) (hr : denote σ right = ⟨w, y⟩) (hlw : left.width = w) (hrw : right.width = w) :
    denote σ (symbolicBinary op left right) = bilBinary op x y := by
  have app := @wordOp_app σ left right w x y hl hr
  cases op
  case sdiv =>
    simp only [symbolicBinary, signedDivision]
    rw [const_zero_of_width hrw, const_ones_of_width hlw, denote_ite, isOne_denote_eq, hr, denote_const]
    by_cases hy : y = 0
    · subst hy
      have : sameBits ⟨w, 0#w⟩ ⟨w, BitVec.ofNat w 0⟩ = true := by simp [sameBits]
      rw [show (0 : BitVec w) = 0#w from rfl, ite_eq_left this]
      simp [bilBinary, Word.sdiv, Word.ones]
    · have : sameBits ⟨w, y⟩ ⟨w, BitVec.ofNat w 0⟩ = false := by
        have hne : y.toNat ≠ 0 := fun e => hy (BitVec.eq_of_toNat_eq (by simpa using e))
        simp [sameBits, hne]
      rw [ite_eq_right (by simp [this])]
      simp only [binaryApp, app, bilBinary]
      simp [wordOp, word_sdiv_smt x y hy]
  all_goals simp [symbolicBinary, binaryApp, app, wordOp, bilBinary, Word.smod]

theorem fst_symbolicBinary (σ : Assignment) (op : Bil.BinOp) {left right : Expr}
    (hl : (denote σ left).1 = left.width) :
    (denote σ (symbolicBinary op left right)).1 = (symbolicBinary op left right).width := by
  have hpred : ∀ name k (l r : Expr), Expr.isPredicate name = true →
      (∀ {w} (x y : BitVec w), (wordOp name x y).1 = 1) → k = 1 →
      (denote σ (.app name k [l, r])).1 = k := by
    intro name k l r hp hw hk
    rw [denote_binary]
    unfold denoteBinary
    split
    · rw [hw, hk]
    · simp [hk]
  have hplain : ∀ name (l r : Expr), Expr.isPredicate name = false → (denote σ l).1 = l.width →
      (∀ {w} (x y : BitVec w), (wordOp name x y).1 = w) →
      (denote σ (.app name l.width [l, r])).1 = l.width := by
    intro name l r hp hl hw
    rw [denote_binary]
    unfold denoteBinary
    split
    · rw [hw, hl]
    · simp [hp, hl]
  have hrem : (denote σ (binaryApp .rem left right)).1 = left.width :=
    hplain _ _ _ (by decide) hl (by intros; simp [wordOp])
  have hremw : (binaryApp .rem left right).width = left.width := rfl
  have hneg : (denote σ (.app "bvneg" left.width [binaryApp .rem left right])).1 = left.width := by
    simp [denote, denoteUnary, hrem]
  cases op
  case sdiv =>
    simp only [symbolicBinary, signedDivision, denote_ite, Expr.width, denote_const]
    split
    · rfl
    · exact hplain _ _ _ (by decide) hl (by intros; simp [wordOp])
  all_goals first
    | exact hplain _ _ _ (by decide) hl (by intros; simp [wordOp])
    | exact hpred _ _ _ _ (by decide) (by intros; simp [wordOp]) rfl

private theorem fst_binary (σ : Assignment) (op : Bil.BinOp) {left right : Expr}
    (hl : (denote σ left).1 = left.width) :
    (denote σ (binary op left right)).1 = (binary op left right).width := by
  rcases binary_cases op left right with h | ⟨_, _, _, _, _, _, _, _, _, h⟩
  · rw [h]; exact fst_symbolicBinary σ op hl
  · rw [h]; rfl

theorem width_evalCast {kind : Bil.Cast} {width : Nat} {value result : Expr}
    (h : evalCast kind width value = .ok result) : result.width = width := by
  unfold evalCast at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h
        simp only [Expr.width]
        omega
    all_goals
      split at h <;> cases h
      · simp only [Expr.width]; omega
      · rfl

theorem evalCast_zero (kind : Bil.Cast) (value : Expr) :
    evalCast kind 0 value = .error "cast width must be positive" := rfl

private theorem extension_name (kind : String) (k : Nat) :
    (s!"(_ {kind} {k})").toList.head? = some '(' := by
  show ("(_ " ++ kind ++ " " ++ toString k ++ ")").toList.head? = _
  simp [String.toList_append]

private theorem extension_ne_literal {kind : String} {k : Nat} {literal : String}
    (h : literal.toList.head? ≠ some '(') : s!"(_ {kind} {k})" ≠ literal := by
  intro e
  rw [← e, extension_name] at h
  exact h rfl

private theorem sign_ne_zero (k : Nat) : s!"(_ {"sign_extend"} {k})" ≠ s!"(_ {"zero_extend"} {k})" := by
  intro e
  have := congrArg String.toList e
  simp [String.toList_append, toString] at this

private theorem zero_ne_sign (k : Nat) : s!"(_ {"zero_extend"} {k})" ≠ s!"(_ {"sign_extend"} {k})" :=
  fun e => sign_ne_zero k e.symm

private theorem denote_extract_of {σ : Assignment} {value : Expr} {w : Nat} {x : BitVec w}
    (h : denote σ value = ⟨w, x⟩) (high low : Nat) :
    denote σ (.extract high low value) = ⟨_, BitVec.extractLsb high low x⟩ := by
  simp only [denote]
  rw [h]

theorem fst_evalCast {σ : Assignment} {kind : Bil.Cast} {width : Nat} {value result : Expr}
    (hv : (denote σ value).1 = value.width) (h : evalCast kind width value = .ok result) :
    (denote σ result).1 = result.width := by
  unfold evalCast at h
  split at h
  · cases h
  · have hunary : ∀ (extension : String) (k : Nat), (extension = "sign_extend" ∨ extension = "zero_extend") →
        (denote σ (.app s!"(_ {extension} {k})" width [value])).1 = width := by
      intro extension k he
      simp only [denote, denoteUnary]
      rw [ite_eq_right (extension_ne_literal (by decide)), ite_eq_right (extension_ne_literal (by decide))]
      repeat' split
      all_goals rfl
    split at h
    · split at h
      · cases h
      · cases h
        simp only [denote, Expr.width]
        omega
    all_goals
      split at h <;> cases h
      · simp only [denote, Expr.width]; omega
      · exact hunary _ _ (by split <;> simp)

theorem width_readCells {cells : List (Expr × Expr)} (h : ∀ cell ∈ cells, cell.2.width = 8)
    (name : String) (address : Expr) : (Memory.readCells name address cells).width = 8 := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    have hc := h cell (by simp)
    have hr := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [Memory.readCells]
    repeat' split
    · exact hc
    · exact hr
    · exact hc

/-- Loads have the width the type checker assigns them. -/
theorem width_read {memory : Bap.Symbolic.Memory} (h : ∀ cell ∈ memory.cells, cell.2.width = 8) (address : Expr)
    (endian : Endian) (size : Nat) : (memory.read address endian size).width = size * 8 := by
  simp only [Bap.Symbolic.Memory.read]
  have hchain : ∀ (bytes : List Expr) (first : Expr),
      (∀ b ∈ bytes, b.width = 8) →
      (bytes.foldl (fun result byte => .concat result byte) first).width = first.width + 8 * bytes.length := by
    intro bytes
    induction bytes with
    | nil => intro first _; simp
    | cons b rest ih =>
      intro first hb
      simp only [List.foldl_cons]
      rw [ih _ fun x hx => hb x (by simp [hx])]
      simp only [Expr.width, List.length_cons, hb b (by simp)]
      omega
  have hbytes : ∀ b ∈ (List.range size).map (fun offset => memory.readByte (offsetAddress address offset)),
      b.width = 8 := by
    intro b hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
    exact width_readCells h _ _
  generalize hl : (List.range size).map (fun offset => memory.readByte (offsetAddress address offset)) = bytes at hbytes ⊢
  have hlen : bytes.length = size := by rw [← hl]; simp
  have horder : (if endian = Bap.Endian.little then bytes.reverse else bytes).length = size ∧
      ∀ b ∈ (if endian = Bap.Endian.little then bytes.reverse else bytes), b.width = 8 := by
    split <;> simp [hlen] <;> simpa using hbytes
  generalize (if endian = Bap.Endian.little then bytes.reverse else bytes) = ordered at horder ⊢
  cases ordered with
  | nil =>
    have := horder.1
    simp at this
    subst this
    rfl
  | cons first rest =>
    simp only
    rw [hchain _ _ fun x hx => horder.2 x (by simp [hx]), horder.2 first (by simp)]
    have := horder.1
    simp at this
    omega

private theorem wellSized_bind {σ : Assignment} {s : State} (h : WellSized σ s) (var : Bap.Var) {x : Expr}
    (hx : (denote σ x).1 = x.width) : WellSized σ { s with env := (var, x) :: s.env } :=
  ⟨fun entry he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hx
      · exact h.envSized entry he,
    h.cellsSized⟩

private theorem wellSized_bindMemory {σ : Assignment} {s : State} (h : WellSized σ s) (var : Bap.Var)
    {m : Bap.Symbolic.Memory} (hm : CellsSized σ m.cells) : WellSized σ { s with memories := (var, m) :: s.memories } :=
  ⟨h.envSized, fun entry he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hm
      · exact h.cellsSized entry he⟩

theorem sized_eval (σ : Assignment) (e : Bil.Exp) :
    (∀ {s : State} {x : Expr}, WellSized σ s → evalExp s e = .ok x → (denote σ x).1 = x.width) ∧
      (∀ {s : State} {memory : Bap.Symbolic.Memory}, WellSized σ s → evalMemory s e = .ok memory →
        CellsSized σ memory.cells) := by
  induction e with
  | int value =>
    refine ⟨fun _ h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, Except.ok.injEq] at h
    subst h; simp [Expr.width]
  | var var =>
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp] at h
      exact hs.envSized _ (get_mem (lookup_ok h).2)
    · simp only [evalMemory] at h
      split at h
      · cases h
        exact cells_memoryOf hs var
      · cases h
  | load memory address endian size ihm iha =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨m, hm, a, ha, h⟩ := h
    cases h
    have hc := ihm.2 hs hm
    rw [(denote_read σ m a endian size hc (iha.1 hs ha)).1, width_read fun c hcell => (hc c hcell).2]
  | store memory address value endian size ihm iha ihv =>
    refine ⟨fun _ h => by simp [evalExp] at h, fun hs h => ?_⟩
    simp only [evalMemory, bind_ok] at h
    obtain ⟨m, hm, a, _, v, _, h⟩ := h
    split at h
    · cases h
    · cases h
      exact cellsSized_write (ihm.2 hs hm) _ _ _ _
  | bin op left right ihl ihr =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, _, h⟩ := h
    cases h
    exact fst_binary σ op (ihl.1 hs hl)
  | un op value ih =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨v, hv, h⟩ := h
    cases h
    have := ih.1 hs hv
    cases op <;> simp [denote, denoteUnary, Expr.width, this]
  | cast kind width value ih =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨v, hv, h⟩ := h
    exact fst_evalCast (ih.1 hs hv) h
  | letIn var value body ihv ihb =>
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp] at h
      split at h
      · obtain ⟨m, hm, h⟩ := bind_ok.mp h
        exact ihb.1 (wellSized_bindMemory hs var (ihv.2 hs hm)) h
      · obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact ihb.1 (wellSized_bind hs var (ihv.1 hs hx)) h
    · simp only [evalMemory] at h
      split at h
      · obtain ⟨m, hm, h⟩ := bind_ok.mp h
        exact ihb.2 (wellSized_bindMemory hs var (ihv.2 hs hm)) h
      · obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact ihb.2 (wellSized_bind hs var (ihv.1 hs hx)) h
  | ite condition yes no _ ihy ihn =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨c, _, y, hy, n, hn, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · next hne =>
        cases h
        have hne' : y.width = n.width := by simpa using hne
        simp only [denote, Expr.width]
        split
        · exact ihy.1 hs hy
        · rw [ihn.1 hs hn, hne']
  | extract high low value _ =>
    refine ⟨fun _ h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [denote, Expr.width]
        omega
  | concat left right ihl ihr =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hr, h⟩ := h
    cases h
    simp only [denote, Expr.width, ihl.1 hs hl, ihr.1 hs hr]
  | unknown message typ =>
    refine ⟨fun _ h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, Except.ok.injEq] at h
    subst h; simp [Expr.width]

/-- Expressions without stores: everything in `Bap.Memory.write` is `partial`, so nothing can be proved of it. -/
def noStore : Bil.Exp → Bool
  | .int _ | .var _ | .unknown _ _ => true
  | .load memory address _ _ => noStore memory && noStore address
  | .store _ _ _ _ _ => false
  | .bin _ left right | .concat left right => noStore left && noStore right
  | .un _ value | .cast _ _ value | .extract _ _ value => noStore value
  | .letIn _ value body => noStore value && noStore body
  | .ite condition yes no => noStore condition && noStore yes && noStore no

/-- What soundness needs of `Bap.Memory.write`, which is built on a `partial` helper and so can't be
proved here. Reads wrap around the address space, and so does the symbolic model; this says writes do too,
which `Bap.Memory.write` doesn't do yet: a store soundness result is only as good as this premise. -/
def StoreSpec : Prop :=
  ∀ {w vw : Nat} (m m' : Bap.Memory w) (a : BitVec w) (v : BitVec vw) (endian : Endian) (size : Nat),
    Bap.Memory.write m a v endian size = .ok m' →
    ∀ address : BitVec w, (Bap.Memory.readByte m' address).toBitVec =
      modelWrite (fun location => if h : location.1 = w then (Bap.Memory.readByte m (h ▸ location.2)).toBitVec else 0)
        ⟨w, a⟩ ⟨vw, v⟩ endian size ⟨w, address⟩

private theorem find_bind_same (env : Bil.Env) (var : Bap.Var) (value : Value) :
    Bil.lookup (Bil.bind env var value) var = .ok value := by
  simp [Bil.lookup, Bil.bind]

private theorem lookup_bind_ne (env : Bil.Env) {var var' : Bap.Var} (value : Value) (h : var' ≠ var) :
    Bil.lookup (Bil.bind env var value) var' = Bil.lookup env var' := by
  have hb : (var == var') = false := by simpa using fun e => h e.symm
  simp only [Bil.lookup, Bil.bind, List.find?_cons, hb]
  have : (env.filter fun binding => binding.1 != var).find? (fun binding => binding.1 == var') =
      env.find? fun binding => binding.1 == var' := by
    induction env with
    | nil => rfl
    | cons entry rest ih =>
      by_cases he : entry.1 = var
      · have hne : (entry.1 == var') = false := by rw [he]; exact hb
        simp [he, hb, ih]
      · simp [he, List.find?_cons, ih]
  rw [this]

private theorem memoryOf_bind_same (s : State) (var : Bap.Var) (m : Bap.Symbolic.Memory) :
    memoryOf { s with memories := (var, m) :: s.memories } var = m := by
  simp [memoryOf, Assoc.get]

private theorem memoryOf_bind_ne (s : State) {var var' : Bap.Var} (m : Bap.Symbolic.Memory) (h : var' ≠ var) :
    memoryOf { s with memories := (var, m) :: s.memories } var' = memoryOf s var' := by
  have hb : (var' == var) = false := by simpa using h
  simp [memoryOf, Assoc.get, List.lookup, hb]

private theorem get_cons_ne {β : Type} (l : List (Bap.Var × β)) {var var' : Bap.Var} (x : β) (h : var' ≠ var) :
    Assoc.get var' ((var, x) :: l) = Assoc.get var' l := by
  have hb : (var' == var) = false := by simpa using h
  simp [Assoc.get, List.lookup, hb]

private theorem get_cons_same {β : Type} (l : List (Bap.Var × β)) (var : Bap.Var) (x : β) :
    Assoc.get var ((var, x) :: l) = some x := by
  simp [Assoc.get]

/-- Binding a bitvector variable keeps a state related to its concrete environment. -/
theorem rel_bind {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) {var : Bap.Var} {x : Expr}
    {value : Value} (hmem : isMemoryType var.typ = false) (hx : (denote σ x).1 = x.width)
    (hv : ∀ {w} {v : BitVec w}, value = .bits v → denote σ x = ⟨w, v⟩) :
    Rel σ { s with env := (var, x) :: s.env } (Bil.bind env var value) where
  toWellSized := wellSized_bind h.toWellSized var hx
  vars := by
    intro var' y w v hm hg hl
    by_cases he : var' = var
    · subst he
      rw [get_cons_same] at hg
      cases hg
      rw [find_bind_same] at hl
      cases hl
      exact hv rfl
    · rw [get_cons_ne _ _ he] at hg
      rw [lookup_bind_ne _ _ he] at hl
      exact h.vars _ _ _ _ hm hg hl
  mems := by
    intro var' w c hm hl
    have he : var' ≠ var := by
      rintro rfl
      rw [hm] at hmem; cases hmem
    rw [lookup_bind_ne _ _ he] at hl
    exact h.mems _ _ _ hm hl

/-- Binding a memory variable keeps a state related to its concrete environment. -/
theorem rel_bindMemory {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) {var : Bap.Var}
    {m : Bap.Symbolic.Memory} {value : Value} (hmem : isMemoryType var.typ = true) (hm : CellsSized σ m.cells)
    (hv : ∀ {w} {c : Bap.Memory w}, value = .memory c → MemRel σ m c) :
    Rel σ { s with memories := (var, m) :: s.memories } (Bil.bind env var value) where
  toWellSized := wellSized_bindMemory h.toWellSized var hm
  vars := by
    intro var' y w v ht hg hl
    have he : var' ≠ var := by
      rintro rfl
      rw [ht] at hmem; cases hmem
    rw [lookup_bind_ne _ _ he] at hl
    exact h.vars _ _ _ _ ht hg hl
  mems := by
    intro var' w c ht hl
    by_cases he : var' = var
    · subst he
      rw [memoryOf_bind_same]
      rw [find_bind_same] at hl
      cases hl
      exact hv rfl
    · rw [memoryOf_bind_ne _ _ he]
      rw [lookup_bind_ne _ _ he] at hl
      exact h.mems _ _ _ ht hl

private theorem modelWrite_congr {f g : ByteMap} {location : Bits} (h : f location = g location)
    (target value : Bits) (endian : Endian) (size : Nat) :
    modelWrite f target value endian size location = modelWrite g target value endian size location := by
  simp only [modelWrite]
  have : ∀ k, (List.range k).foldl (init := f) (fun bytes offset location =>
        if sameBits (offsetBits target offset) location then
          valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
        else bytes location) location =
      (List.range k).foldl (init := g) (fun bytes offset location =>
        if sameBits (offsetBits target offset) location then
          valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
        else bytes location) location := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [modelWrite_succ, modelWrite_succ]
      simp only [ih]
  exact this size

private theorem fold_toBitVec (bytes : List UInt8) :
    bytes.foldl (fun result byte => result * 256 + byte.toNat) 0 =
      (bytes.map UInt8.toBitVec).foldl (fun result byte => result * 256 + byte.toNat) 0 := by
  rw [List.foldl_map]
  rfl

/-- A load through related memories denotes the concrete load. -/
theorem denote_read_concrete {σ : Assignment} {memory : Bap.Symbolic.Memory} {w : Nat} {concrete : Bap.Memory w}
    (hrel : MemRel σ memory concrete) (hcells : CellsSized σ memory.cells) {address : Expr} {a : BitVec w}
    (hd : denote σ address = ⟨w, a⟩) (hw : address.width = w) (endian : Endian) (size : Nat) :
    denote σ (memory.read address endian size) = ⟨size * 8, Bap.Memory.read concrete a endian size⟩ := by
  obtain ⟨h1, h2⟩ := denote_read σ memory address endian size hcells (by rw [hd, hw])
  refine bits_ext h1 ?_
  rw [h2, hd]
  have hbound := toNat_lt_of_width h1
  rw [h2, hd] at hbound
  have hbytes : ((List.range size).map fun offset =>
      Bap.Memory.readByte concrete (a + BitVec.ofNat w offset)).map UInt8.toBitVec =
      (List.range size).map fun offset =>
        byteMap σ memory.name memory.cells (offsetBits ⟨w, a⟩ offset) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro offset _
    exact hrel _
  simp only [Bap.Memory.read, BitVec.toNat_ofNat]
  cases endian with
  | little =>
    simp only [modelRead] at hbound ⊢
    rw [fold_toBitVec, List.map_reverse, hbytes]
    exact (Nat.mod_eq_of_lt hbound).symm
  | big =>
    simp only [modelRead] at hbound ⊢
    rw [fold_toBitVec, hbytes]
    exact (Nat.mod_eq_of_lt hbound).symm

private theorem denote_binary_sound {σ : Assignment} {op : Bil.BinOp} {left right : Expr} {lw rw w : Nat}
    {lv : BitVec lw} {rv : BitVec rw} {v : BitVec w}
    (hl : denote σ left = ⟨lw, lv⟩) (hr : denote σ right = ⟨rw, rv⟩) (hlw : left.width = lw) (hrw : right.width = rw)
    (h : Bil.evalBin op ⟨lw, lv⟩ ⟨rw, rv⟩ = .ok (.bits v)) :
    denote σ (binary op left right) = ⟨w, v⟩ := by
  rcases binary_cases op left right with he | ⟨a, av, b, bv, c, cv, rfl, rfl, hf, he⟩
  · by_cases hwidth : lw = rw
    · subst hwidth
      obtain ⟨v', hv', hb⟩ := evalBin_same op lv rv
      rw [hv'] at h
      cases h
      rw [he, denote_symbolicBinary op hl hr hlw hrw]
      exact hb.symm
    · simp [Bil.evalBin, hwidth] at h
  · rw [he]
    rw [denote_const] at hl hr
    cases hl
    cases hr
    rw [hf] at h
    cases h
    simp

private theorem denote_truncate {σ : Assignment} {x : Expr} {w width : Nat} {v : BitVec w}
    (hd : denote σ x = ⟨w, v⟩) (hpos : width ≠ 0) :
    denote σ (.extract (width - 1) 0 x) = ⟨width, BitVec.zeroExtend width v⟩ := by
  rw [denote_extract_of hd]
  apply bits_ext (by simp only; omega)
  simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  congr 2
  omega

private theorem denote_extension {σ : Assignment} {x : Expr} {w width : Nat} {v : BitVec w}
    (hd : denote σ x = ⟨w, v⟩) (hw : x.width = w) :
    denote σ (.app s!"(_ {"sign_extend"} {width - x.width})" width [x]) = ⟨width, BitVec.signExtend width v⟩ ∧
      denote σ (.app s!"(_ {"zero_extend"} {width - x.width})" width [x]) = ⟨width, BitVec.zeroExtend width v⟩ := by
  have hunary : ∀ name, denote σ (.app name width [x]) = denoteUnary name width (denote σ x) := by
    intro name; simp [denote]
  have n1 : ∀ (kind : String) (k : Nat), s!"(_ {kind} {k})" ≠ "bvneg" := fun _ _ => extension_ne_literal (by decide)
  have n2 : ∀ (kind : String) (k : Nat), s!"(_ {kind} {k})" ≠ "bvnot" := fun _ _ => extension_ne_literal (by decide)
  rw [hunary, hunary, hd, hw]
  simp only [denoteUnary, n1, n2, zero_ne_sign, ↓reduceIte]
  constructor <;> first | trivial | rfl

private theorem denote_evalCast {σ : Assignment} {x : Expr} {w width : Nat} {v : BitVec w} {r : Expr}
    (hd : denote σ x = ⟨w, v⟩) (hw : x.width = w) (kind : Bil.Cast) (h : evalCast kind width x = .ok r) :
    match kind with
    | .low | .unsigned => denote σ r = ⟨width, BitVec.zeroExtend width v⟩
    | .signed => denote σ r = ⟨width, BitVec.signExtend width v⟩
    | .high => ∀ result, Word.high width v = .ok result → denote σ r = ⟨width, result⟩ := by
  have ⟨hsign, hzero⟩ := denote_extension (width := width) hd hw
  unfold evalCast at h
  split at h
  · cases h
  · next hz =>
    cases kind
    case high =>
      simp only at h
      rw [hw] at h
      split at h
      · cases h
      · next hle =>
        cases h
        intro result hres
        simp only [Word.high] at hres
        split at hres
        · cases hres
          rw [denote_extract_of hd]
          apply bits_ext (by simp only; omega)
          simp only [BitVec.extractLsb_toNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
          congr 2
          omega
        · cases hres
    all_goals
      simp only at h
      split at h
      · next hle =>
        cases h
        first
          | exact denote_truncate hd hz
          | (rw [denote_truncate hd hz, BitVec.signExtend_eq_setWidth_of_le _ (by omega)])
      · cases h
        first
          | exact hzero
          | exact hsign

private theorem isOne_one_iff (c : BitVec 1) : isOne ⟨1, c⟩ = true ↔ c = 1 := by
  simp only [isOne, beq_iff_eq]
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl; rfl

/-- Soundness of expression evaluation: under any assignment related to the concrete environment, the
symbolic value of an expression denotes its concrete value. -/
theorem evalExp_sound (σ : Assignment) (e : Bil.Exp) (hs : StoreSpec ∨ noStore e = true) :
    (∀ {s : State} {env : Bil.Env} {x : Expr} {w : Nat} {v : BitVec w}, Rel σ s env → evalExp s e = .ok x →
      Bil.evalExp env e = .ok (.bits v) → denote σ x = ⟨w, v⟩) ∧
    (∀ {s : State} {env : Bil.Env} {memory : Bap.Symbolic.Memory} {w : Nat} {c : Bap.Memory w}, Rel σ s env →
      evalMemory s e = .ok memory → Bil.evalExp env e = .ok (.memory c) → MemRel σ memory c) := by
  induction e with
  | int value =>
    refine ⟨fun _ h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, Except.ok.injEq] at h
    simp only [Bil.evalExp, Except.ok.injEq] at hc
    subst h
    cases hc
    simp
  | var var =>
    refine ⟨fun hr h hc => ?_, fun hr h hc => ?_⟩
    · simp only [evalExp] at h
      obtain ⟨hm, hg⟩ := lookup_ok h
      simp only [Bil.evalExp] at hc
      exact hr.vars _ _ _ _ hm hg hc
    · simp only [evalMemory] at h
      split at h
      · next hm =>
        cases h
        simp only [Bil.evalExp] at hc
        exact hr.mems _ _ _ hm hc
      · cases h
  | load memory address endian size ihm iha =>
    have hs' : StoreSpec ∨ noStore memory = true := hs.imp id (fun h => by simp_all [noStore])
    have hsa : StoreSpec ∨ noStore address = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨m, hm, a, ha, h⟩ := h
    cases h
    simp only [Bil.evalExp, bind_ok] at hc
    obtain ⟨mv, hmv, ⟨mw, cm⟩, hexp, av, hav, ⟨aw, addr⟩, hbits, hc⟩ := hc
    cases mv <;> simp only [expectMemory, reduceCtorEq] at hexp
    cases hexp
    cases av <;> simp only [Value.asBits, reduceCtorEq] at hbits
    cases hbits
    simp only at hc
    by_cases hw : aw = mw
    · subst hw
      simp only [↓reduceDIte, Except.ok.injEq] at hc
      cases hc
      have hma := (iha hsa).1 hr ha hav
      have hsa' := (sized_eval σ address).1 hr.toWellSized ha
      rw [hma] at hsa'
      exact denote_read_concrete ((ihm hs').2 hr hm hmv) ((sized_eval σ memory).2 hr.toWellSized hm) hma hsa'.symm _ _
    · simp [hw] at hc
  | store memory address value endian size ihm iha ihv =>
    refine ⟨fun _ h _ => by simp [evalExp] at h, fun hr h hc => ?_⟩
    have hspec : StoreSpec := hs.resolve_right (by simp [noStore])
    simp only [evalMemory, bind_ok] at h
    obtain ⟨m, hm, a, ha, x, hx, h⟩ := h
    split at h
    · cases h
    · cases h
      simp only [Bil.evalExp, bind_ok] at hc
      obtain ⟨mv, hmv, ⟨mw, cm⟩, hexp, av, hav, ⟨aw, addr⟩, hbits, vv, hvv, ⟨vw, val⟩, hvbits, hc⟩ := hc
      cases mv <;> simp only [expectMemory, reduceCtorEq] at hexp
      cases hexp
      cases av <;> simp only [Value.asBits, reduceCtorEq] at hbits
      cases hbits
      cases vv <;> simp only [Value.asBits, reduceCtorEq] at hvbits
      cases hvbits
      simp only at hc
      by_cases hw : aw = mw
      · subst hw
        simp only [↓reduceDIte] at hc
        obtain ⟨updated, hu, hc⟩ := bind_ok.mp hc
        cases hc
        have hma := (iha (.inl hspec)).1 hr ha hav
        have hmx := (ihv (.inl hspec)).1 hr hx hvv
        have hrelm := (ihm (.inl hspec)).2 hr hm hmv
        have hsa := (sized_eval σ address).1 hr.toWellSized ha
        intro location
        rw [hspec _ _ _ _ _ _ hu location, name_write, byteMap_write σ m a x endian size hsa, hma, hmx]
        exact (modelWrite_congr (by simpa using (hrelm location).symm) _ _ _ _).symm
      · simp [hw] at hc
  | bin op left right ihl ihr =>
    have hsl : StoreSpec ∨ noStore left = true := hs.imp id (fun h => by simp_all [noStore])
    have hsr : StoreSpec ∨ noStore right = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr' h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hrr, h⟩ := h
    cases h
    simp only [Bil.evalExp, bind_ok] at hc
    obtain ⟨lv, hlv, ⟨lw, lb⟩, hlb, rv, hrv, ⟨rw, rb⟩, hrb, hc⟩ := hc
    cases lv <;> simp only [Value.asBits, reduceCtorEq] at hlb
    cases hlb
    cases rv <;> simp only [Value.asBits, reduceCtorEq] at hrb
    cases hrb
    have hdl := (ihl hsl).1 hr' hl hlv
    have hdr := (ihr hsr).1 hr' hrr hrv
    have hwl := (sized_eval σ left).1 hr'.toWellSized hl
    have hwr := (sized_eval σ right).1 hr'.toWellSized hrr
    rw [hdl] at hwl
    rw [hdr] at hwr
    exact denote_binary_sound hdl hdr hwl.symm hwr.symm hc
  | un op value ih =>
    have hs' : StoreSpec ∨ noStore value = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    cases h
    simp only [Bil.evalExp, bind_ok] at hc
    obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
    cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
    cases hcb
    have hdx := (ih hs').1 hr hx hcv
    have hunary : ∀ name k, denote σ (.app name k [x]) = denoteUnary name k (denote σ x) := by
      intro name k; simp [denote]
    rw [hunary, hdx]
    cases op <;> simp only [evalUn, Except.ok.injEq] at hc <;> cases hc <;> simp [denoteUnary]
  | cast kind width value ih =>
    have hs' : StoreSpec ∨ noStore value = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    simp only [Bil.evalExp, bind_ok] at hc
    obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
    cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
    cases hcb
    have hdx := (ih hs').1 hr hx hcv
    have hwx := (sized_eval σ value).1 hr.toWellSized hx
    rw [hdx] at hwx
    have := denote_evalCast hdx hwx.symm kind h
    cases kind
    case high =>
      obtain ⟨result, hres, hc⟩ := bind_ok.mp hc
      cases hc
      exact this _ hres
    all_goals
      cases hc
      exact this
  | letIn var value body ihv ihb =>
    have hsv : StoreSpec ∨ noStore value = true := hs.imp id (fun h => by simp_all [noStore])
    have hsb : StoreSpec ∨ noStore body = true := hs.imp id (fun h => by simp_all [noStore])
    have bits : ∀ {s : State} {env : Bil.Env} {x : Expr} {cv : Value}, Rel σ s env →
        isMemoryType var.typ = false → evalExp s value = .ok x → Bil.evalExp env value = .ok cv →
        Rel σ { s with env := (var, x) :: s.env } (Bil.bind env var cv) := by
      intro s env x cv hr hmem hx hcv
      exact rel_bind hr hmem ((sized_eval σ value).1 hr.toWellSized hx)
        (fun he => (ihv hsv).1 hr hx (he ▸ hcv))
    have mem : ∀ {s : State} {env : Bil.Env} {m : Bap.Symbolic.Memory} {cv : Value}, Rel σ s env →
        isMemoryType var.typ = true → evalMemory s value = .ok m → Bil.evalExp env value = .ok cv →
        Rel σ { s with memories := (var, m) :: s.memories } (Bil.bind env var cv) := by
      intro s env m cv hr hmem hm hcv
      exact rel_bindMemory hr hmem ((sized_eval σ value).2 hr.toWellSized hm)
        (fun he => (ihv hsv).2 hr hm (he ▸ hcv))
    refine ⟨fun hr h hc => ?_, fun hr h hc => ?_⟩
    · simp only [evalExp] at h
      simp only [Bil.evalExp, bind_ok] at hc
      obtain ⟨cv, hcv, hc⟩ := hc
      split at h
      · next hm =>
        obtain ⟨m, hm', h⟩ := bind_ok.mp h
        exact (ihb hsb).1 (mem hr hm hm' hcv) h hc
      · next hm =>
        obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact (ihb hsb).1 (bits hr (by simpa using hm) hx hcv) h hc
    · simp only [evalMemory] at h
      simp only [Bil.evalExp, bind_ok] at hc
      obtain ⟨cv, hcv, hc⟩ := hc
      split at h
      · next hm =>
        obtain ⟨m, hm', h⟩ := bind_ok.mp h
        exact (ihb hsb).2 (mem hr hm hm' hcv) h hc
      · next hm =>
        obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact (ihb hsb).2 (bits hr (by simpa using hm) hx hcv) h hc
  | ite condition yes no ihc ihy ihn =>
    have hsc : StoreSpec ∨ noStore condition = true := hs.imp id (fun h => by simp_all [noStore])
    have hsy : StoreSpec ∨ noStore yes = true := hs.imp id (fun h => by simp_all [noStore])
    have hsn : StoreSpec ∨ noStore no = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨c, hcond, y, hy, n, hn, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [Bil.evalExp, bind_ok] at hc
        obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
        cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
        cases hcb
        simp only at hc
        by_cases hw : cw = 1
        · subst hw
          have hdc := (ihc hsc).1 hr hcond hcv
          rw [denote_ite, hdc]
          simp only [↓reduceDIte] at hc
          by_cases h1 : cb = 1
          · rw [ite_eq_left h1] at hc
            rw [ite_eq_left ((isOne_one_iff cb).mpr h1)]
            exact (ihy hsy).1 hr hy hc
          · rw [ite_eq_right h1] at hc
            rw [ite_eq_right (fun e => h1 ((isOne_one_iff cb).mp e))]
            exact (ihn hsn).1 hr hn hc
        · simp [hw] at hc
  | extract high low value ih =>
    have hs' : StoreSpec ∨ noStore value = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [Bil.evalExp, bind_ok] at hc
        obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, res, hres, hc⟩ := hc
        cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
        cases hcb
        cases hc
        have hdx := (ih hs').1 hr hx hcv
        rw [denote_extract_of hdx]
        simp only [Word.extract] at hres
        split at hres
        · cases hres
        · split at hres
          · cases hres
          · cases hres; rfl
  | concat left right ihl ihr =>
    have hsl : StoreSpec ∨ noStore left = true := hs.imp id (fun h => by simp_all [noStore])
    have hsr : StoreSpec ∨ noStore right = true := hs.imp id (fun h => by simp_all [noStore])
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hrr, h⟩ := h
    cases h
    simp only [Bil.evalExp, bind_ok] at hc
    obtain ⟨lv, hlv, ⟨lw, lb⟩, hlb, rv, hrv, ⟨rw, rb⟩, hrb, hc⟩ := hc
    cases lv <;> simp only [Value.asBits, reduceCtorEq] at hlb
    cases hlb
    cases rv <;> simp only [Value.asBits, reduceCtorEq] at hrb
    cases hrb
    cases hc
    have hdl := (ihl hsl).1 hr hl hlv
    have hdr := (ihr hsr).1 hr hrr hrv
    simp only [denote]
    rw [hdl, hdr]
    rfl
  | unknown message typ =>
    refine ⟨fun _ _ hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp [Bil.evalExp] at hc

/-! ### Execution: every concrete run is covered by a path -/

/-- Expressions with no `unknown`: those the concrete evaluator has a value for on every branch. -/
def noUnknown : Bil.Exp → Bool
  | .int _ | .var _ => true
  | .unknown _ _ => false
  | .load memory address _ _ => noUnknown memory && noUnknown address
  | .store memory address value _ _ => noUnknown memory && noUnknown address && noUnknown value
  | .bin _ left right | .concat left right => noUnknown left && noUnknown right
  | .un _ value | .cast _ _ value | .extract _ _ value => noUnknown value
  | .letIn _ value body => noUnknown value && noUnknown body
  | .ite condition yes no => noUnknown condition && noUnknown yes && noUnknown no

theorem freshenUnknowns_of_noUnknown (e : Bil.Exp) (next : Nat) (h : noUnknown e = true) :
    freshenUnknowns next e = (e, next) := by
  induction e generalizing next <;>
    simp_all [freshenUnknowns, noUnknown]

private theorem freshen_of_noUnknown (s : State) (e : Bil.Exp) (h : noUnknown e = true) : freshen s e = (s, e) := by
  simp [freshen, freshenUnknowns_of_noUnknown e _ h]

/-- The programs covered: every expression is free of `unknown`, and either free of stores or `StoreSpec` holds. -/
def ExpFragment (e : Bil.Exp) : Prop := noUnknown e = true ∧ (StoreSpec ∨ noStore e = true)

mutual
  def stmtFragment : Bil.Stmt → Prop
    | .move _ value => ExpFragment value
    | .jmp target => ExpFragment target
    | .special _ | .cpuExn _ => True
    | .ifElse condition yes no => ExpFragment condition ∧ programFragment yes ∧ programFragment no
    | .while condition body => ExpFragment condition ∧ programFragment body

  def programFragment : Bil.Program → Prop
    | [] => True
    | stmt :: rest => stmtFragment stmt ∧ programFragment rest
end

/-- The path condition of a state holds under an assignment. -/
def PathHolds (σ : Assignment) (s : State) : Prop := ∀ c ∈ s.constraints, Holds σ c

/-- The symbolic and concrete ways a statement can end correspond. -/
def OutcomeMatches (σ : Assignment) : Outcome → Bil.Effect → Prop
  | .normal, .normal => True
  | .jump target, .jump concrete => denote σ target = ⟨_, concrete⟩
  | .special message, .special concrete => message = concrete
  | .cpuExn number, .cpuExn concrete => number = concrete
  | _, _ => False

/-- A path accounts for a concrete run if its condition holds and it ends the same way in a related state,
or if the exploration bound stopped it first. -/
def Covers (σ : Assignment) (results : List Result) (final : Bil.State × Bil.Effect) : Prop :=
  ∃ r ∈ results, PathHolds σ r.state ∧
    (r.outcome = .exhausted ∨ (Rel σ r.state final.1.env ∧ OutcomeMatches σ r.outcome final.2))

private theorem covers_of_subset {σ : Assignment} {as bs : List Result} {final : Bil.State × Bil.Effect}
    (h : ∀ x ∈ as, x ∈ bs) (hc : Covers σ as final) : Covers σ bs final :=
  let ⟨r, hr, hp⟩ := hc
  ⟨r, h r hr, hp⟩

private theorem rel_withConstraint {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) (c : Expr) :
    Rel σ (withConstraint s c) env :=
  { envSized := h.envSized, cellsSized := h.cellsSized, vars := h.vars, mems := h.mems }

private theorem pathHolds_withConstraint {σ : Assignment} {s : State} (h : PathHolds σ s) {c : Expr}
    (hc : Holds σ c) : PathHolds σ (withConstraint s c) := by
  intro x hx
  simp only [withConstraint, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x hx
  · exact hc

private theorem expectCondition_ok {x y : Expr} (h : expectCondition x = .ok y) : y = x ∧ x.width = 1 := by
  unfold expectCondition at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

private theorem bit_cases (c : BitVec 1) : c = 1 ∨ c = 0 := by
  have := c.isLt
  by_cases h : c.toNat = 1
  · exact .inl (BitVec.eq_of_toNat_eq (by simpa using h))
  · exact .inr (BitVec.eq_of_toNat_eq (by simp; omega))

private theorem known_sound {σ : Assignment} {x : Expr} {b : Bool} {c : BitVec 1}
    (hk : x.knownCondition = some b) (hd : denote σ x = ⟨1, c⟩) : c = 1 ↔ b = true := by
  cases x <;> simp only [Expr.knownCondition, reduceCtorEq] at hk
  next w v =>
    split at hk
    · next hw =>
      subst hw
      rw [denote_const] at hd
      cases hd
      simp only [Option.some.injEq] at hk
      subst hk
      simp only [beq_iff_eq]
      exact ⟨fun e => by rw [e]; rfl, fun e => BitVec.eq_of_toNat_eq (by simpa using e)⟩
    · cases hk

private theorem holds_eqOne {σ : Assignment} {x : Expr} (hw : x.width = 1) (hd : denote σ x = ⟨1, 1⟩) :
    Holds σ (Expr.eqOne x) := by
  rw [eqOne_of_width_one hw, Holds, hd]; rfl

private theorem holds_eqZero {σ : Assignment} {x : Expr} (hw : x.width = 1) (hd : denote σ x = ⟨1, 0⟩) :
    Holds σ (Expr.eqZero x) := by
  simp only [Holds, Expr.eqZero]
  rw [const_zero_of_width hw, isOne_denote_eq, hd, denote_const]
  rfl

private theorem continueProgram_cons (f : Nat) (rest : Bil.Program) (a : Result) (others : List Result) :
    executeProgram.continueResults f rest (a :: others) = (do
      let first ← (match a.outcome with
        | .normal => executeProgram f a.state rest
        | _ => .ok [a])
      let others ← executeProgram.continueResults f rest others
      .ok (first ++ others)) := by
  rw [executeProgram.continueResults]
  cases a.outcome <;> rfl

private theorem continueWhile_cons (f : Nat) (c : Bil.Exp) (body : Bil.Program) (a : Result) (others : List Result) :
    executeStmt.continueResults f c body (a :: others) = (do
      let first ← (match a.outcome with
        | .normal => executeStmt f a.state (.while c body)
        | _ => .ok [a])
      let others ← executeStmt.continueResults f c body others
      .ok (first ++ others)) := by
  rw [executeStmt.continueResults]
  cases a.outcome <;> rfl

private theorem continueProgram_normal {f : Nat} {rest : Bil.Program} {results qs : List Result} {r : Result}
    (h : executeProgram.continueResults f rest results = .ok qs) (hr : r ∈ results) (hn : r.outcome = .normal) :
    ∃ first, executeProgram f r.state rest = .ok first ∧ ∀ x ∈ first, x ∈ qs := by
  induction results generalizing qs with
  | nil => cases hr
  | cons a others ih =>
    rw [continueProgram_cons] at h
    obtain ⟨first, hf, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [hn] at hf
      exact ⟨first, hf, fun x hx => List.mem_append_left _ hx⟩
    · obtain ⟨first', hf', hs⟩ := ih ho hr
      exact ⟨first', hf', fun x hx => List.mem_append_right _ (hs x hx)⟩

private theorem continueProgram_other {f : Nat} {rest : Bil.Program} {results qs : List Result} {r : Result}
    (h : executeProgram.continueResults f rest results = .ok qs) (hr : r ∈ results) (hn : ¬ r.outcome = .normal) :
    r ∈ qs := by
  induction results generalizing qs with
  | nil => cases hr
  | cons a others ih =>
    rw [continueProgram_cons] at h
    obtain ⟨first, hf, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    rcases List.mem_cons.mp hr with rfl | hr
    · split at hf
      · next he => exact absurd he hn
      · cases hf; simp
    · exact List.mem_append_right _ (ih ho hr)

private theorem continueWhile_normal {f : Nat} {c : Bil.Exp} {body : Bil.Program} {results qs : List Result} {r : Result}
    (h : executeStmt.continueResults f c body results = .ok qs) (hr : r ∈ results) (hn : r.outcome = .normal) :
    ∃ first, executeStmt f r.state (.while c body) = .ok first ∧ ∀ x ∈ first, x ∈ qs := by
  induction results generalizing qs with
  | nil => cases hr
  | cons a others ih =>
    rw [continueWhile_cons] at h
    obtain ⟨first, hf, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [hn] at hf
      exact ⟨first, hf, fun x hx => List.mem_append_left _ hx⟩
    · obtain ⟨first', hf', hs⟩ := ih ho hr
      exact ⟨first', hf', fun x hx => List.mem_append_right _ (hs x hx)⟩

private theorem continueWhile_other {f : Nat} {c : Bil.Exp} {body : Bil.Program} {results qs : List Result} {r : Result}
    (h : executeStmt.continueResults f c body results = .ok qs) (hr : r ∈ results) (hn : ¬ r.outcome = .normal) :
    r ∈ qs := by
  induction results generalizing qs with
  | nil => cases hr
  | cons a others ih =>
    rw [continueWhile_cons] at h
    obtain ⟨first, hf, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    rcases List.mem_cons.mp hr with rfl | hr
    · split at hf
      · next he => exact absurd he hn
      · cases hf; simp
    · exact List.mem_append_right _ (ih ho hr)

theorem executeProgram_nil (f : Nat) (s : State) : executeProgram f s [] = .ok [⟨s, .normal⟩] := by
  cases f <;> rw [executeProgram]

theorem executeStmt_zero (s : State) (stmt : Bil.Stmt) : executeStmt 0 s stmt = .ok [⟨s, .exhausted⟩] := by
  rw [executeStmt]

theorem executeProgram_zero_cons (s : State) (stmt : Bil.Stmt) (rest : Bil.Program) :
    executeProgram 0 s (stmt :: rest) = .ok [⟨s, .exhausted⟩] := by
  rw [executeProgram]

private theorem outcome_normal_of_matches {σ : Assignment} {o : Outcome} (h : OutcomeMatches σ o .normal) :
    o = .normal := by
  cases o <;> first | rfl | exact h.elim

private theorem outcome_other_of_matches {σ : Assignment} {o : Outcome} {e : Bil.Effect}
    (h : OutcomeMatches σ o e) (he : ¬ e matches .normal) : ¬ o = .normal := by
  rintro rfl
  cases e with
  | normal => simp at he
  | jump _ => exact h
  | special _ => exact h
  | cpuExn _ => exact h

/-- Sequencing keeps coverage: a covered statement followed by a covered program. -/
private theorem covers_sequence {σ : Assignment} {sf cf : Nat} {rest : Bil.Program} {results qs : List Result}
    {next : Bil.State} {effect : Bil.Effect} {final : Bil.State × Bil.Effect}
    (hrest : ∀ s rs final, Rel σ s next.env → PathHolds σ s → executeProgram sf s rest = .ok rs →
      Bil.execProgram cf next rest = .ok final → Covers σ rs final)
    (hcover : Covers σ results (next, effect))
    (hq : executeProgram.continueResults sf rest results = .ok qs)
    (hfinal : (match effect with
      | .normal => Bil.execProgram cf next rest
      | other => .ok (next, other)) = Except.ok final) :
    Covers σ qs final := by
  obtain ⟨r, hr, hp, hend⟩ := hcover
  rcases hend with hx | ⟨hrel, hm⟩
  · exact ⟨r, continueProgram_other hq hr (by rw [hx]; simp), hp, .inl hx⟩
  · cases effect
    case normal =>
      obtain ⟨first, hf, hs⟩ := continueProgram_normal hq hr (outcome_normal_of_matches hm)
      exact covers_of_subset hs (hrest _ _ _ hrel hp hf hfinal)
    all_goals
      cases hfinal
      exact ⟨r, continueProgram_other hq hr (outcome_other_of_matches hm (by simp)), hp, .inr ⟨hrel, hm⟩⟩

/-- Symbolic execution is sound: every concrete run of a statement or program, from a state an assignment
relates to the symbolic state and whose path condition it satisfies, is covered by a symbolic path. Holds for
loops too, where the bound may stop the path. -/
theorem execute_sound (σ : Assignment) (cf : Nat) :
    (∀ (sf : Nat) (s : State) (stmt : Bil.Stmt) (env : Bil.Env) (rs : List Result) (final : Bil.State × Bil.Effect),
      stmtFragment stmt → Rel σ s env → PathHolds σ s → executeStmt sf s stmt = .ok rs →
      Bil.execStmt cf { env := env } stmt = .ok final → Covers σ rs final) ∧
    (∀ (sf : Nat) (s : State) (program : Bil.Program) (env : Bil.Env) (rs : List Result) (final : Bil.State × Bil.Effect),
      programFragment program → Rel σ s env → PathHolds σ s → executeProgram sf s program = .ok rs →
      Bil.execProgram cf { env := env } program = .ok final → Covers σ rs final) := by
  induction cf with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ hc => ?_, fun _ _ _ _ _ _ _ _ _ _ hc => ?_⟩
    · rw [Bil.execStmt] at hc; cases hc
    · rw [Bil.execProgram] at hc; cases hc
  | succ cf ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro sf s stmt env rs final hfrag hrel hpath hsym hc
      cases sf with
      | zero =>
        rw [executeStmt_zero] at hsym
        cases hsym
        exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inl rfl⟩
      | succ sf =>
        cases stmt with
        | move var value =>
          obtain ⟨hu, hst⟩ : ExpFragment value := hfrag
          rw [executeStmt, freshen_of_noUnknown _ _ hu] at hsym
          rw [Bil.execStmt] at hc
          obtain ⟨cv, hcv, hc⟩ := bind_ok.mp hc
          cases hc
          have hsound := evalExp_sound σ value hst
          simp only at hsym
          split at hsym
          · next hm =>
            obtain ⟨m, hm', hsym⟩ := bind_ok.mp hsym
            cases hsym
            refine ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨?_, trivial⟩⟩
            exact rel_bindMemory hrel hm ((sized_eval σ value).2 hrel.toWellSized hm')
              (fun he => hsound.2 hrel hm' (he ▸ hcv))
          · next hm =>
            obtain ⟨x, hx, hsym⟩ := bind_ok.mp hsym
            cases hsym
            refine ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨?_, trivial⟩⟩
            exact rel_bind hrel (by simpa using hm) ((sized_eval σ value).1 hrel.toWellSized hx)
              (fun he => hsound.1 hrel hx (he ▸ hcv))
        | jmp target =>
          obtain ⟨hu, hst⟩ : ExpFragment target := hfrag
          rw [executeStmt, freshen_of_noUnknown _ _ hu] at hsym
          rw [Bil.execStmt] at hc
          simp only [bind_ok] at hc
          obtain ⟨cv, hcv, ⟨w, t⟩, hb, hc⟩ := hc
          cases cv <;> simp only [Value.asBits, reduceCtorEq] at hb
          cases hb
          cases hc
          obtain ⟨x, hx, hsym⟩ := bind_ok.mp hsym
          cases hsym
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, (evalExp_sound σ target hst).1 hrel hx hcv⟩⟩
        | special message =>
          rw [executeStmt] at hsym
          rw [Bil.execStmt] at hc
          cases hsym
          cases hc
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, rfl⟩⟩
        | cpuExn number =>
          rw [executeStmt] at hsym
          rw [Bil.execStmt] at hc
          cases hsym
          cases hc
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, rfl⟩⟩
        | ifElse condition yes no =>
          obtain ⟨⟨hu, hst⟩, hfy, hfn⟩ : ExpFragment condition ∧ programFragment yes ∧ programFragment no := hfrag
          rw [executeStmt, freshen_of_noUnknown _ _ hu] at hsym
          rw [Bil.execStmt] at hc
          simp only [bind_ok] at hc
          obtain ⟨cv, hcv, ⟨w, t⟩, hb, hc⟩ := hc
          cases cv <;> simp only [Value.asBits, reduceCtorEq] at hb
          cases hb
          simp only at hc
          by_cases hw : w = 1
          · subst hw
            simp only [↓reduceDIte] at hc
            simp only [bind_ok] at hsym
            obtain ⟨x0, hx0, x, hx, hsym⟩ := hsym
            obtain ⟨rfl, hxw⟩ := expectCondition_ok hx
            have hd := (evalExp_sound σ condition hst).1 hrel hx0 hcv
            cases hk : x.knownCondition with
            | some b =>
              rw [hk] at hsym
              have hkb := known_sound hk hd
              cases b
              · have ht : ¬ t = 1 := by simpa using hkb
                rw [ite_eq_right ht] at hc
                exact ihp _ _ _ _ _ _ hfn hrel hpath hsym hc
              · have ht : t = 1 := by simpa using hkb
                rw [ite_eq_left ht] at hc
                exact ihp _ _ _ _ _ _ hfy hrel hpath hsym hc
            | none =>
              rw [hk] at hsym
              simp only [bind_ok] at hsym
              obtain ⟨ys, hy, ns, hn, hsym⟩ := hsym
              cases hsym
              rcases bit_cases t with rfl | rfl
              · rw [ite_eq_left rfl] at hc
                exact covers_of_subset (fun _ h => List.mem_append_left _ h)
                  (ihp _ _ _ _ _ _ hfy (rel_withConstraint hrel _)
                    (pathHolds_withConstraint hpath (holds_eqOne hxw hd)) hy hc)
              · rw [ite_eq_right (by decide)] at hc
                exact covers_of_subset (fun _ h => List.mem_append_right _ h)
                  (ihp _ _ _ _ _ _ hfn (rel_withConstraint hrel _)
                    (pathHolds_withConstraint hpath (holds_eqZero hxw hd)) hn hc)
          · simp [hw] at hc
        | «while» condition body =>
          have hfrag' := hfrag
          obtain ⟨⟨hu, hst⟩, hfb⟩ : ExpFragment condition ∧ programFragment body := hfrag
          rw [executeStmt, freshen_of_noUnknown _ _ hu] at hsym
          rw [Bil.execStmt] at hc
          simp only [bind_ok] at hc
          obtain ⟨cv, hcv, ⟨w, t⟩, hb, hc⟩ := hc
          cases cv <;> simp only [Value.asBits, reduceCtorEq] at hb
          cases hb
          simp only at hc
          by_cases hw : w = 1
          · subst hw
            simp only [↓reduceDIte] at hc
            simp only [bind_ok] at hsym
            obtain ⟨x0, hx0, x, hx, hsym⟩ := hsym
            obtain ⟨rfl, hxw⟩ := expectCondition_ok hx
            have hd := (evalExp_sound σ condition hst).1 hrel hx0 hcv
            have hloop : ∀ {results qs : List Result} {next : Bil.State × Bil.Effect},
                Covers σ results next →
                executeStmt.continueResults sf condition body results = .ok qs →
                (match next.2 with
                  | .normal => Bil.execStmt cf next.1 (.while condition body)
                  | other => .ok (next.1, other)) = Except.ok final →
                Covers σ qs final := by
              intro results qs next hcover hq hfinal
              obtain ⟨r, hr, hp, hend⟩ := hcover
              rcases hend with hxh | ⟨hrelr, hm⟩
              · exact ⟨r, continueWhile_other hq hr (by rw [hxh]; simp), hp, .inl hxh⟩
              · obtain ⟨nextState, effect⟩ := next
                simp only at hfinal hrelr hm
                cases effect
                case normal =>
                  obtain ⟨first, hf, hsub⟩ := continueWhile_normal hq hr (outcome_normal_of_matches hm)
                  exact covers_of_subset hsub (ihs _ _ _ _ _ _ hfrag' hrelr hp hf hfinal)
                all_goals
                  cases hfinal
                  exact ⟨r, continueWhile_other hq hr (outcome_other_of_matches hm (by simp)), hp, .inr ⟨hrelr, hm⟩⟩
            cases hk : x.knownCondition with
            | some b =>
              rw [hk] at hsym
              have hkb := known_sound hk hd
              cases b
              · have ht : ¬ t = 1 := by simpa using hkb
                rw [ite_eq_right ht] at hc
                cases hc
                cases hsym
                exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, trivial⟩⟩
              · have ht : t = 1 := by simpa using hkb
                rw [ite_eq_left ht] at hc
                obtain ⟨⟨next, effect⟩, hbody, hc⟩ := bind_ok.mp hc
                obtain ⟨bs, hbs, hq⟩ := bind_ok.mp hsym
                exact hloop (next := (next, effect)) (ihp _ _ _ _ _ _ hfb hrel hpath hbs hbody) hq hc
            | none =>
              rw [hk] at hsym
              simp only [bind_ok] at hsym
              obtain ⟨bs, hbs, qs, hq, hsym⟩ := hsym
              cases hsym
              rcases bit_cases t with rfl | rfl
              · rw [ite_eq_left rfl] at hc
                obtain ⟨⟨next, effect⟩, hbody, hc⟩ := bind_ok.mp hc
                exact covers_of_subset (fun _ h => List.mem_append_left _ h)
                  (hloop (next := (next, effect)) (ihp _ _ _ _ _ _ hfb (rel_withConstraint hrel _)
                    (pathHolds_withConstraint hpath (holds_eqOne hxw hd)) hbs hbody) hq hc)
              · rw [ite_eq_right (by decide)] at hc
                cases hc
                exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl),
                  pathHolds_withConstraint hpath (holds_eqZero hxw hd), .inr ⟨rel_withConstraint hrel _, trivial⟩⟩
          · simp [hw] at hc
    · intro sf s program env rs final hfrag hrel hpath hsym hc
      cases program with
      | nil =>
        rw [executeProgram_nil] at hsym
        rw [Bil.execProgram] at hc
        cases hsym
        cases hc
        exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, trivial⟩⟩
      | cons stmt rest =>
        obtain ⟨hfs, hfr⟩ : stmtFragment stmt ∧ programFragment rest := hfrag
        cases sf with
        | zero =>
          rw [executeProgram_zero_cons] at hsym
          cases hsym
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inl rfl⟩
        | succ sf =>
          rw [executeProgram] at hsym
          rw [Bil.execProgram] at hc
          obtain ⟨results, hres, hq⟩ := bind_ok.mp hsym
          obtain ⟨⟨next, effect⟩, hstmt, hc⟩ := bind_ok.mp hc
          obtain ⟨nextEnv⟩ := next
          exact covers_sequence (next := { env := nextEnv }) (effect := effect)
            (fun s' rs' final' hr hp hsy hcn => ihp _ _ _ _ _ _ hfr hr hp hsy hcn)
            (ihs _ _ _ _ _ _ hfs hrel hpath hres hstmt) hq hc

/-- The states an assignment can stand for: its variables are inputs with the assignment's values, and the
memories hold the assignment's initial contents. -/
theorem rel_inputs (σ : Assignment) (env : Bil.Env) (inputs : Env) (hinputs : ∀ entry ∈ inputs,
      (denote σ entry.2).1 = entry.2.width ∧ ∀ w (v : BitVec w), isMemoryType entry.1.typ = false →
        Bil.lookup env entry.1 = .ok (.bits v) → denote σ entry.2 = ⟨w, v⟩)
    (hmemory : ∀ var w (c : Bap.Memory w), isMemoryType var.typ = true → Bil.lookup env var = .ok (.memory c) →
      ∀ address : BitVec w, (Bap.Memory.readByte c address).toBitVec = σ.memory s!"{var.name}#{var.index}" w address) :
    Rel σ { env := inputs } env where
  envSized := fun entry he => (hinputs entry he).1
  cellsSized := fun entry he => by cases he
  vars := by
    intro var x w v hm hg hl
    exact (hinputs (var, x) (get_mem hg)).2 w v hm hl
  mems := by
    intro var w c hm hl address
    simpa [memoryOf, Assoc.get, byteMap] using hmemory var w c hm hl address

/-! ### Loop-free programs are explored completely -/

mutual
  /-- The nesting of a program without loops, which bounds the fuel it needs. -/
  def stmtDepth : Bil.Stmt → Nat
    | .ifElse _ yes no => 1 + max (programDepth yes) (programDepth no)
    | _ => 1

  def programDepth : Bil.Program → Nat
    | [] => 0
    | stmt :: rest => 1 + max (stmtDepth stmt) (programDepth rest)
end

mutual
  def stmtLoopFree : Bil.Stmt → Prop
    | .while _ _ => False
    | .ifElse _ yes no => programLoopFree yes ∧ programLoopFree no
    | _ => True

  def programLoopFree : Bil.Program → Prop
    | [] => True
    | stmt :: rest => stmtLoopFree stmt ∧ programLoopFree rest
end

private theorem stmtDepth_pos (stmt : Bil.Stmt) : 0 < stmtDepth stmt := by
  cases stmt <;> simp [stmtDepth] <;> omega

private theorem continueProgram_mem {f : Nat} {rest : Bil.Program} {results qs : List Result} {q : Result}
    (h : executeProgram.continueResults f rest results = .ok qs) (hq : q ∈ qs) :
    ∃ r ∈ results, (∃ first, r.outcome = .normal ∧ executeProgram f r.state rest = .ok first ∧ q ∈ first) ∨
      (¬ r.outcome = .normal ∧ q = r) := by
  induction results generalizing qs with
  | nil =>
    rw [executeProgram.continueResults] at h
    cases h
    cases hq
  | cons a others ih =>
    rw [continueProgram_cons] at h
    obtain ⟨first, hf, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    rcases List.mem_append.mp hq with hq | hq
    · refine ⟨a, by simp, ?_⟩
      cases hn : a.outcome
      case normal =>
        rw [hn] at hf
        exact .inl ⟨first, rfl, hf, hq⟩
      all_goals
        rw [hn] at hf
        cases hf
        exact .inr ⟨by simp, by simpa using hq⟩
    · obtain ⟨r, hr, he⟩ := ih ho hq
      exact ⟨r, List.mem_cons_of_mem _ hr, he⟩

private theorem continueWhile_mem {f : Nat} {c : Bil.Exp} {body : Bil.Program} {results qs : List Result} {q : Result}
    (h : executeStmt.continueResults f c body results = .ok qs) (hq : q ∈ qs) :
    ∃ r ∈ results, (∃ first, r.outcome = .normal ∧ executeStmt f r.state (.while c body) = .ok first ∧ q ∈ first) ∨
      (¬ r.outcome = .normal ∧ q = r) := by
  induction results generalizing qs with
  | nil =>
    rw [executeStmt.continueResults] at h
    cases h
    cases hq
  | cons a others ih =>
    rw [continueWhile_cons] at h
    obtain ⟨first, hf, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    rcases List.mem_append.mp hq with hq | hq
    · refine ⟨a, by simp, ?_⟩
      cases hn : a.outcome
      case normal =>
        rw [hn] at hf
        exact .inl ⟨first, rfl, hf, hq⟩
      all_goals
        rw [hn] at hf
        cases hf
        exact .inr ⟨by simp, by simpa using hq⟩
    · obtain ⟨r, hr, he⟩ := ih ho hq
      exact ⟨r, List.mem_cons_of_mem _ hr, he⟩

/-- With fuel for its depth, a loop-free program reports no exhausted path: all of its paths are finished. -/
theorem execute_complete_of_depth (f : Nat) :
    (∀ s stmt rs, stmtLoopFree stmt → stmtDepth stmt ≤ f → executeStmt f s stmt = .ok rs →
      ∀ r ∈ rs, r.outcome ≠ .exhausted) ∧
    (∀ s program rs, programLoopFree program → programDepth program ≤ f → executeProgram f s program = .ok rs →
      ∀ r ∈ rs, r.outcome ≠ .exhausted) := by
  induction f with
  | zero =>
    refine ⟨fun _ stmt _ _ hd _ => ?_, fun s program rs _ hd h => ?_⟩
    · have := stmtDepth_pos stmt; omega
    · cases program with
      | nil =>
        rw [executeProgram_nil] at h
        cases h
        intro r hr
        rw [List.mem_singleton.mp hr]
        simp
      | cons stmt rest => simp [programDepth] at hd
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro s stmt rs hfree hd h
      cases stmt with
      | «while» c b => exact hfree.elim
      | move var value =>
        rw [executeStmt] at h
        simp only at h
        split at h
        all_goals
          obtain ⟨_, _, h⟩ := bind_ok.mp h
          cases h
          intro r hr
          rw [List.mem_singleton.mp hr]
          simp
      | jmp target =>
        rw [executeStmt] at h
        simp only at h
        obtain ⟨_, _, h⟩ := bind_ok.mp h
        cases h
        intro r hr
        rw [List.mem_singleton.mp hr]
        simp
      | special m =>
        rw [executeStmt] at h
        cases h
        intro r hr
        rw [List.mem_singleton.mp hr]
        simp
      | cpuExn n =>
        rw [executeStmt] at h
        cases h
        intro r hr
        rw [List.mem_singleton.mp hr]
        simp
      | ifElse c yes no =>
        obtain ⟨hfy, hfn⟩ : programLoopFree yes ∧ programLoopFree no := hfree
        have hdy : programDepth yes ≤ f := by simp [stmtDepth] at hd; omega
        have hdn : programDepth no ≤ f := by simp [stmtDepth] at hd; omega
        rw [executeStmt] at h
        simp only [bind_ok] at h
        obtain ⟨_, _, x, _, h⟩ := h
        split at h
        · exact ihp _ _ _ hfy hdy h
        · exact ihp _ _ _ hfn hdn h
        · simp only [bind_ok] at h
          obtain ⟨ys, hy, ns, hn, h⟩ := h
          cases h
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact ihp _ _ _ hfy hdy hy r hr
          · exact ihp _ _ _ hfn hdn hn r hr
    · intro s program rs hfree hd h
      cases program with
      | nil =>
        rw [executeProgram_nil] at h
        cases h
        intro r hr
        rw [List.mem_singleton.mp hr]
        simp
      | cons stmt rest =>
        obtain ⟨hfs, hfr⟩ : stmtLoopFree stmt ∧ programLoopFree rest := hfree
        have hds : stmtDepth stmt ≤ f := by simp [programDepth] at hd; omega
        have hdr : programDepth rest ≤ f := by simp [programDepth] at hd; omega
        rw [executeProgram] at h
        obtain ⟨results, hres, hq⟩ := bind_ok.mp h
        intro q hqm
        obtain ⟨r, hr, he⟩ := continueProgram_mem hq hqm
        rcases he with ⟨first, _, hf, hqf⟩ | ⟨_, rfl⟩
        · exact ihp _ _ _ hfr hdr hf q hqf
        · exact ihs _ _ _ hfs hds hres q hr

/-- The headline: symbolic execution of a loop-free program is sound against the BIL evaluator. Every concrete
run corresponds to a path whose condition the concrete inputs satisfy, whose final state denotes the concrete
state, and which ends the same way. -/
theorem run_sound_loop_free (σ : Assignment) {program : Bil.Program} {s : State} {env : Bil.Env} {rs : List Result}
    {final : Bil.State × Bil.Effect} {sf cf : Nat} (hfrag : programFragment program) (hfree : programLoopFree program)
    (hdepth : programDepth program ≤ sf) (hrel : Rel σ s env) (hpath : PathHolds σ s)
    (hsym : run program s sf = .ok rs) (hc : Bil.run program { env := env } cf = .ok final) :
    ∃ r ∈ rs, PathHolds σ r.state ∧ Rel σ r.state final.1.env ∧ OutcomeMatches σ r.outcome final.2 := by
  obtain ⟨r, hr, hp, hend⟩ := (execute_sound σ cf).2 sf s program env rs final hfrag hrel hpath hsym hc
  rcases hend with he | he
  · exact absurd he ((execute_complete_of_depth sf).2 s program rs hfree hdepth hsym r hr)
  · exact ⟨r, hr, hp, he⟩

/-! ### All paths survive -/

/-- Sequencing continues every normal result and keeps every other result. -/
theorem continueResults_cons_normal (f : Nat) (rest : Bil.Program) (r : Result) (others : List Result)
    (h : r.outcome = .normal) :
    executeProgram.continueResults f rest (r :: others) = (do
      let first ← executeProgram f r.state rest
      let others ← executeProgram.continueResults f rest others
      .ok (first ++ others)) := by
  rw [continueProgram_cons, h]

theorem continueResults_cons_other (f : Nat) (rest : Bil.Program) (r : Result) (others : List Result)
    (h : ¬ r.outcome = .normal) :
    executeProgram.continueResults f rest (r :: others) = (do
      let others ← executeProgram.continueResults f rest others
      .ok (r :: others)) := by
  rw [continueProgram_cons]
  cases hn : r.outcome
  case normal => exact absurd hn h
  all_goals rfl

theorem executeStmt_ifElse_empty {s : State} {c : Bil.Exp} {x : Expr} (f : Nat) (hu : noUnknown c = true)
    (h : evalExp s c = .ok x) (hw : x.width = 1) (hk : x.knownCondition = none) :
    executeStmt (f + 1) s (.ifElse c [] []) =
      .ok [⟨withConstraint s x.eqOne, .normal⟩, ⟨withConstraint s x.eqZero, .normal⟩] := by
  have he : expectCondition x = .ok x := by simp [expectCondition, hw]
  rw [executeStmt, freshen_of_noUnknown _ _ hu]
  simp [h, he, hk, bind, Except.bind, executeProgram_nil]

/-- A symbolic branch yields both paths, each under its condition, and what follows runs on both. -/
theorem executeProgram_ifElse_both {s : State} {c : Bil.Exp} {x : Expr} (f : Nat) (rest : Bil.Program)
    (hu : noUnknown c = true) (h : evalExp s c = .ok x) (hw : x.width = 1) (hk : x.knownCondition = none) :
    executeProgram (f + 2) s (.ifElse c [] [] :: rest) = (do
      let yes ← executeProgram (f + 1) (withConstraint s x.eqOne) rest
      let no ← executeProgram (f + 1) (withConstraint s x.eqZero) rest
      .ok (yes ++ no)) := by
  rw [executeProgram, executeStmt_ifElse_empty _ hu h hw hk]
  simp only [bind, Except.bind, continueProgram_cons]
  have : executeProgram.continueResults (f + 1) rest [] = .ok [] := by
    rw [executeProgram.continueResults]
  simp only [this, List.append_nil]
  cases executeProgram (f + 1) (withConstraint s x.eqOne) rest <;>
    cases executeProgram (f + 1) (withConstraint s x.eqZero) rest <;> rfl

/-- So `if b then {} else {}` has two results, one per branch. -/
theorem run_ifElse_both {s : State} {c : Bil.Exp} {x : Expr} (f : Nat) (hu : noUnknown c = true)
    (h : evalExp s c = .ok x) (hw : x.width = 1) (hk : x.knownCondition = none) :
    run [.ifElse c [] []] s (f + 2) =
      .ok [⟨withConstraint s x.eqOne, .normal⟩, ⟨withConstraint s x.eqZero, .normal⟩] := by
  show executeProgram (f + 2) s _ = _
  rw [executeProgram_ifElse_both f [] hu h hw hk, executeProgram_nil, executeProgram_nil]
  rfl

/-- A condition known to be false ends a loop at once, with no change at all to the state. -/
theorem executeStmt_while_false {s : State} {c : Bil.Exp} {x : Expr} (f : Nat) (body : Bil.Program)
    (hu : noUnknown c = true) (h : evalExp s c = .ok x) (hw : x.width = 1) (hk : x.knownCondition = some false) :
    executeStmt (f + 1) s (.while c body) = .ok [⟨s, .normal⟩] := by
  have he : expectCondition x = .ok x := by simp [expectCondition, hw]
  rw [executeStmt, freshen_of_noUnknown _ _ hu]
  simp [h, he, hk, bind, Except.bind]

theorem run_while_false (s : State) (f : Nat) (body : Bil.Program) :
    run [.while (.int (0#1)) body] s (f + 2) = .ok [⟨s, .normal⟩] := by
  show executeProgram (f + 2) s _ = _
  rw [executeProgram, executeStmt_while_false f body rfl rfl rfl rfl]
  simp only [bind, Except.bind, continueProgram_cons, executeProgram_nil]
  rw [executeProgram.continueResults]
  rfl

/-- A loop that never ends is reported through its bound, not as a failure of the run. -/
theorem executeStmt_while_true_exhausted (f : Nat) (s : State) :
    executeStmt f s (.while (.int (1#1)) []) = .ok [⟨s, .exhausted⟩] := by
  induction f with
  | zero => exact executeStmt_zero s _
  | succ f ih =>
    have he : expectCondition (.const (1#1)) = .ok (.const (1#1)) := rfl
    rw [executeStmt, freshen_of_noUnknown _ _ rfl]
    simp only [evalExp, bind, Except.bind, he]
    show (executeProgram f s [] >>= _) = _
    rw [executeProgram_nil]
    simp only [bind, Except.bind, continueWhile_cons, ih]
    rw [executeStmt.continueResults]
    rfl

/-- Exhaustion is an ordinary result, whatever the program. -/
theorem run_zero_fuel (stmt : Bil.Stmt) (rest : Bil.Program) (s : State) :
    run (stmt :: rest) s 0 = .ok [⟨s, .exhausted⟩] := executeProgram_zero_cons s stmt rest

/-- Unknown values drawn in sequence are separate variables. -/
theorem freshen_unknown_names (next : Nat) (message : String) (typ : Typ) :
    freshenUnknowns next (.unknown message typ) = (.unknown s!"{message}#{next}" typ, next + 1) := rfl

/-- Each memory variable has its own store: a write to one leaves the rest of them alone. -/
theorem memoryOf_write_frame (s : State) {var other : Bap.Var} (m : Bap.Symbolic.Memory) (h : other ≠ var) :
    memoryOf { s with memories := (var, m) :: s.memories } other = memoryOf s other :=
  memoryOf_bind_ne s m h

/-- The initial contents of different memory variables are different functions. -/
theorem memoryOf_initial_name (s : State) (var : Bap.Var) (h : Assoc.get var s.memories = none) :
    (memoryOf s var).name = s!"{var.name}#{var.index}" ∧ (memoryOf s var).cells = [] := by
  simp [memoryOf, h]

/-! ### Invariants of execution -/

/-- A property of states preserved by every primitive state change the executor makes. -/
structure StepInvariant (Inv : State → Prop) : Prop where
  constraint : ∀ s (x : Expr), x.width = 1 → Inv s →
    Inv (withConstraint s x.eqOne) ∧ Inv (withConstraint s x.eqZero)
  unknowns : ∀ s n, Inv s → Inv { s with unknowns := n }
  move : ∀ s var value x, Inv s → evalExp s value = .ok x → Inv { s with env := (var, x) :: s.env }
  memory : ∀ s var value m, Inv s → evalMemory s value = .ok m → Inv { s with memories := (var, m) :: s.memories }

private theorem freshen_eq (s : State) (e : Bil.Exp) :
    freshen s e = ({ s with unknowns := (freshenUnknowns s.unknowns e).2 }, (freshenUnknowns s.unknowns e).1) := rfl

/-- Induction principle for the executor: step invariants hold on every result of every path. -/
theorem execute_preserves {Inv : State → Prop} (hinv : StepInvariant Inv) (f : Nat) :
    (∀ s stmt rs, Inv s → executeStmt f s stmt = .ok rs → ∀ r ∈ rs, Inv r.state) ∧
      (∀ s program rs, Inv s → executeProgram f s program = .ok rs → ∀ r ∈ rs, Inv r.state) := by
  have single : ∀ {t : State} {o : Outcome} {r : Result}, Inv t → r ∈ [(⟨t, o⟩ : Result)] → Inv r.state := by
    intro t o r ht hr
    rw [List.mem_singleton.mp hr]
    exact ht
  induction f with
  | zero =>
    refine ⟨fun s stmt rs hs h => ?_, fun s program rs hs h => ?_⟩
    · rw [executeStmt_zero] at h
      cases h
      exact fun r hr => single hs hr
    · cases program with
      | nil =>
        rw [executeProgram_nil] at h
        cases h
        exact fun r hr => single hs hr
      | cons stmt rest =>
        rw [executeProgram_zero_cons] at h
        cases h
        exact fun r hr => single hs hr
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    refine ⟨fun s stmt rs hs h => ?_, fun s program rs hs h => ?_⟩
    · cases stmt with
      | move var value =>
        rw [executeStmt, freshen_eq] at h
        have hs' := hinv.unknowns s (freshenUnknowns s.unknowns value).2 hs
        simp only at h
        split at h
        · obtain ⟨m, hm, he⟩ := bind_ok.mp h
          cases he
          exact fun r hr => single (hinv.memory _ _ _ _ hs' hm) hr
        · obtain ⟨x, hx, he⟩ := bind_ok.mp h
          cases he
          exact fun r hr => single (hinv.move _ _ _ _ hs' hx) hr
      | jmp target =>
        rw [executeStmt, freshen_eq] at h
        have hs' := hinv.unknowns s (freshenUnknowns s.unknowns target).2 hs
        simp only at h
        obtain ⟨_, _, he⟩ := bind_ok.mp h
        cases he
        exact fun r hr => single hs' hr
      | special message =>
        rw [executeStmt] at h
        cases h
        exact fun r hr => single hs hr
      | cpuExn number =>
        rw [executeStmt] at h
        cases h
        exact fun r hr => single hs hr
      | ifElse condition yes no =>
        rw [executeStmt, freshen_eq] at h
        have hs' := hinv.unknowns s (freshenUnknowns s.unknowns condition).2 hs
        simp only [bind_ok] at h
        obtain ⟨x0, _, x, hx, h⟩ := h
        obtain ⟨rfl, hw⟩ := expectCondition_ok hx
        split at h
        · exact ihp _ _ _ hs' h
        · exact ihp _ _ _ hs' h
        · simp only [bind_ok] at h
          obtain ⟨ys, hy, ns, hn, he⟩ := h
          cases he
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact ihp _ _ _ (hinv.constraint _ _ hw hs').1 hy r hr
          · exact ihp _ _ _ (hinv.constraint _ _ hw hs').2 hn r hr
      | «while» condition body =>
        rw [executeStmt, freshen_eq] at h
        have hs' := hinv.unknowns s (freshenUnknowns s.unknowns condition).2 hs
        simp only [bind_ok] at h
        obtain ⟨x0, _, x, hx, h⟩ := h
        obtain ⟨rfl, hw⟩ := expectCondition_ok hx
        have hcont : ∀ {results qs : List Result}, (∀ r ∈ results, Inv r.state) →
            executeStmt.continueResults f condition body results = .ok qs → ∀ q ∈ qs, Inv q.state := by
          intro results qs hall hq q hqm
          obtain ⟨r, hr, he⟩ := continueWhile_mem hq hqm
          rcases he with ⟨first, _, hf, hqf⟩ | ⟨_, rfl⟩
          · exact ihs _ _ _ (hall r hr) hf q hqf
          · exact hall _ hr
        split at h
        · obtain ⟨bs, hb, hq⟩ := bind_ok.mp h
          exact hcont (ihp _ _ _ hs' hb) hq
        · cases h
          exact fun r hr => single hs' hr
        · simp only [bind_ok] at h
          obtain ⟨bs, hb, qs, hq, he⟩ := h
          cases he
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hcont (ihp _ _ _ (hinv.constraint _ _ hw hs').1 hb) hq r hr
          · exact single (hinv.constraint _ _ hw hs').2 hr
    · cases program with
      | nil =>
        rw [executeProgram_nil] at h
        cases h
        exact fun r hr => single hs hr
      | cons stmt rest =>
        rw [executeProgram] at h
        obtain ⟨results, hres, hq⟩ := bind_ok.mp h
        intro q hqm
        obtain ⟨r, hr, he⟩ := continueProgram_mem hq hqm
        rcases he with ⟨first, _, hf, hqf⟩ | ⟨_, rfl⟩
        · exact ihp _ _ _ (ihs _ _ _ hs hres r hr) hf q hqf
        · exact ihs _ _ _ hs hres _ hr

private theorem prefix_invariant (base : List Expr) :
    StepInvariant fun s => base <+: s.constraints where
  constraint := fun _ _ _ h => ⟨h.trans (List.prefix_append _ _), h.trans (List.prefix_append _ _)⟩
  unknowns := fun _ _ h => h
  move := fun _ _ _ _ h _ => h
  memory := fun _ _ _ _ h _ => h

/-- Path conditions only grow: every result extends the constraints it started from. -/
theorem executeProgram_constraints_prefix {f : Nat} {s : State} {program : Bil.Program} {rs : List Result}
    (h : executeProgram f s program = .ok rs) : ∀ r ∈ rs, s.constraints <+: r.state.constraints :=
  (execute_preserves (prefix_invariant s.constraints) f).2 s program rs (List.prefix_refl _) h

theorem executeStmt_constraints_prefix {f : Nat} {s : State} {stmt : Bil.Stmt} {rs : List Result}
    (h : executeStmt f s stmt = .ok rs) : ∀ r ∈ rs, s.constraints <+: r.state.constraints :=
  (execute_preserves (prefix_invariant s.constraints) f).1 s stmt rs (List.prefix_refl _) h

/-- All path constraints added by execution are one-bit, given one-bit initial constraints. -/
theorem executeProgram_constraints_one_bit {f : Nat} {s : State} {program : Bil.Program} {rs : List Result}
    (h : executeProgram f s program = .ok rs) (hs : ∀ c ∈ s.constraints, c.width = 1) :
    ∀ r ∈ rs, ∀ c ∈ r.state.constraints, c.width = 1 := by
  refine (execute_preserves (Inv := fun s => ∀ c ∈ s.constraints, c.width = 1) ⟨?_, ?_, ?_, ?_⟩ f).2 s program rs hs h
  · intro s x hw hs
    constructor <;> intro y hy <;> simp only [withConstraint, List.mem_append, List.mem_singleton] at hy
    · rcases hy with hy | rfl
      · exact hs y hy
      · exact width_eqOne x hw
    · rcases hy with hy | rfl
      · exact hs y hy
      · exact width_eqZero x
  · exact fun _ _ h => h
  · exact fun _ _ _ _ h _ => h
  · exact fun _ _ _ _ h _ => h

/-- Expressions and memories stay sized along every path, under any assignment. -/
theorem executeProgram_wellSized (σ : Assignment) {f : Nat} {s : State} {program : Bil.Program} {rs : List Result}
    (h : executeProgram f s program = .ok rs) (hs : WellSized σ s) : ∀ r ∈ rs, WellSized σ r.state := by
  refine (execute_preserves (Inv := WellSized σ) ⟨?_, ?_, ?_, ?_⟩ f).2 s program rs hs h
  · exact fun _ _ _ h => ⟨⟨h.envSized, h.cellsSized⟩, ⟨h.envSized, h.cellsSized⟩⟩
  · exact fun _ _ h => ⟨h.envSized, h.cellsSized⟩
  · intro s var value x h hx
    exact wellSized_bind h var ((sized_eval σ value).1 h hx)
  · intro s var value m h hm
    exact wellSized_bindMemory h var ((sized_eval σ value).2 h hm)

theorem executeStmt_special (f : Nat) (s : State) (message : String) :
    executeStmt (f + 1) s (.special message) = .ok [⟨s, .special message⟩] := by
  rw [executeStmt]

theorem executeStmt_cpuExn (f : Nat) (s : State) (number : Nat) :
    executeStmt (f + 1) s (.cpuExn number) = .ok [⟨s, .cpuExn number⟩] := by
  rw [executeStmt]

/-! ### Reading back a write -/

private theorem sameBits_offset_ne {t : Bits} {j k : Nat} (hj : j < 2 ^ t.1) (hk : k < 2 ^ t.1) (h : j ≠ k) :
    sameBits (offsetBits t j) (offsetBits t k) = false := by
  obtain ⟨w, x⟩ := t
  cases he : sameBits (offsetBits ⟨w, x⟩ j) (offsetBits ⟨w, x⟩ k) with
  | false => rfl
  | true =>
    have e := sameBits_iff.mp he
    simp only [offsetBits, Sigma.mk.injEq, heq_eq_eq, true_and] at e
    have e' : BitVec.ofNat w j = BitVec.ofNat w k := by simpa using e
    have := congrArg BitVec.toNat e'
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] at this
    exact absurd this h

/-- A write covers each of its offsets with the matching byte, while it doesn't wrap around the addresses. -/
theorem modelWrite_offset (bytes : ByteMap) (target value : Bits) (endian : Endian) {size k : Nat}
    (hsize : size ≤ 2 ^ target.1) (hk : k < size) :
    modelWrite bytes target value endian size (offsetBits target k) =
      valueByte value (match endian with | .little => k | .big => size - 1 - k) := by
  simp only [modelWrite]
  have : ∀ n, n ≤ size → k < n →
      (List.range n).foldl (init := bytes) (fun bytes offset location =>
        if sameBits (offsetBits target offset) location then
          valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
        else bytes location) (offsetBits target k) =
      valueByte value (match endian with | .little => k | .big => size - 1 - k) := by
    intro n
    induction n with
    | zero => intro _ h; omega
    | succ n ih =>
      intro hn hlt
      rw [modelWrite_succ]
      simp only
      by_cases he : n = k
      · subst he
        have : sameBits (offsetBits target n) (offsetBits target n) = true := sameBits_iff.mpr rfl
        rw [ite_eq_left this]
      · rw [ite_eq_right (by simp [sameBits_offset_ne (t := target) (j := n) (k := k) (by omega) (by omega) he])]
        exact ih (by omega) (by omega)
  exact this size (Nat.le_refl _) hk

private theorem fold_bytes (value : Nat) (k : Nat) (acc : Nat) :
    (((List.range k).reverse.map fun index => BitVec.ofNat 8 (value >>> (index * 8))).foldl
      (fun result byte => result * 256 + byte.toNat) acc) = acc * 2 ^ (8 * k) + value % 2 ^ (8 * k) := by
  induction k generalizing acc with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.map_cons, List.foldl_cons]
    rw [ih]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have hp : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    have hs : 2 ^ (k * 8) = 2 ^ (8 * k) := by rw [Nat.mul_comm]
    rw [hs, hp]
    generalize 2 ^ (8 * k) = P
    have hm : value % (P * 256) = (value / P % 256) * P + value % P := by
      rw [Nat.mod_mul, Nat.mul_comm P, Nat.add_comm]
    rw [hm, show (2 : Nat) ^ 8 = 256 by rfl]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 P]
    omega

private theorem reverse_range_eq (n : Nat) :
    (List.range n).reverse = (List.range n).map (n - 1 - ·) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h1
  simp

/-- Reading back a write yields the value's low `size` bytes, in either byte order and under any assignment,
as long as the write does not wrap around the address space. Writes through other addresses are not assumed away:
this is about the byte map, and any aliasing is in it. -/
theorem read_write_denote (σ : Assignment) (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian)
    {size : Nat} (hcells : CellsSized σ memory.cells) (ha : (denote σ address).1 = address.width)
    (hsize : size ≤ 2 ^ address.width) :
    (denote σ ((memory.write address value endian size).read address endian size)).2.toNat =
      (denote σ value).2.toNat % 2 ^ (8 * size) := by
  rw [(denote_read σ _ address endian size (cellsSized_write hcells _ _ _ _) ha).2, name_write]
  simp only [modelRead]
  have hbytes : ((List.range size).map fun offset =>
      byteMap σ memory.name (memory.write address value endian size).cells (offsetBits (denote σ address) offset)) =
      (List.range size).map fun offset =>
        valueByte (denote σ value) (match endian with | .little => offset | .big => size - 1 - offset) := by
    apply List.map_congr_left
    intro offset hoff
    rw [byteMap_write σ memory address value endian size ha,
      modelWrite_offset _ _ _ _ (by rw [ha]; exact hsize) (List.mem_range.mp hoff)]
    cases endian <;> rfl
  have hfold := fold_bytes (denote σ value).2.toNat size 0
  simp only [Nat.zero_mul, Nat.zero_add] at hfold
  rw [hbytes]
  cases endian with
  | little =>
    simp only [List.map_reverse.symm, valueByte]
    rw [← hfold]
  | big =>
    simp only [valueByte]
    rw [← hfold, reverse_range_eq, List.map_map]
    rfl

end Bap.Proofs.Symbolic
