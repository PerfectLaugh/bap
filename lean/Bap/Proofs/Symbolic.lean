import Lean.Elab.Command
import Bap.Symbolic.Executor
import Bap.Bil.Typecheck
import Bap.Proofs.Core

set_option linter.unusedSimpArgs false

namespace Bap.Proofs.Symbolic

open Lean Elab Command in
/-- Bind short names to private declarations of an imported module (`open private` lives in Batteries). -/
local elab "open_private_decls " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

open Bap.Symbolic
open_private_decls Bap.Symbolic.Memory Bap.Symbolic.Memory offsetAddress byteAt
open_private_decls Bap.Symbolic.Executor Bap.Symbolic lookup binaryApp binary evalCast
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
  else if name = "bvsdiv" then ⟨w, Word.sdiv x y⟩
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

/-- BIL's signed division is SMT-LIB's, for every divisor. -/
theorem word_sdiv_smt {w : Nat} (x y : BitVec w) : Word.sdiv x y = BitVec.smtSDiv x y := rfl

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
def byteMap (σ : Assignment) (initial : Bits → BitVec 8) : List (Expr × Expr) → Bits → BitVec 8
  | [], target => initial target
  | cell :: rest, target =>
    if sameBits (denote σ cell.1) target then byteOf σ cell.2 else byteMap σ initial rest target

/-- The initial contents of a memory: the assignment's, or the chosen memory's for a conditional one. -/
def baseByte (σ : Assignment) : Bap.Symbolic.Memory → Bits → BitVec 8
  | ⟨name, none, _⟩, target => σ.memory name target.1 target.2
  | ⟨_, some (condition, yes, no), _⟩, target =>
    if isOne (denote σ condition) then byteMap σ (baseByte σ yes) yes.cells target
    else byteMap σ (baseByte σ no) no.cells target

/-- The concrete bytes of a symbolic memory. -/
def memoryByte (σ : Assignment) (memory : Bap.Symbolic.Memory) : Bits → BitVec 8 :=
  byteMap σ (baseByte σ memory) memory.cells

def CellsSized (σ : Assignment) (cells : List (Expr × Expr)) : Prop :=
  ∀ cell ∈ cells, (denote σ cell.2).1 = 8 ∧ cell.2.width = 8 ∧ (denote σ cell.1).1 = cell.1.width

private theorem toNat_lt_of_width {b : Bits} {n : Nat} (h : b.1 = n) : b.2.toNat < 2 ^ n := by
  obtain ⟨w, x⟩ := b
  simp only at h
  subst h
  exact x.isLt

private theorem denote_offset_parts {σ : Assignment} (name : String) {width v : Nat} {base : Expr} {c : BitVec v}
    (hname : Expr.isPredicate name = false) (hop : ∀ {w} (x y : BitVec w), (wordOp name x y).1 = w) (_ : v = width)
    (hs : (denote σ (.app name width [base, .const c])).1 = width) :
    (denote σ base).1 = width := by
  rw [denote_binary, denote_const] at hs
  unfold denoteBinary at hs
  split at hs
  · rw [hop] at hs; exact hs
  · simpa [hname] using hs

/-- `baseOffset` splits an address into a base and an offset with the same value, modulo the address space. -/
theorem baseOffset_spec (σ : Assignment) (e : Expr) (h : (denote σ e).1 = e.width) :
    (denote σ (Memory.baseOffset e).1).1 = e.width ∧ (Memory.baseOffset e).2 < 2 ^ e.width ∧
      (denote σ e).2.toNat = ((denote σ (Memory.baseOffset e).1).2.toNat + (Memory.baseOffset e).2) % 2 ^ e.width := by
  have hrefl : ∀ {e : Expr}, (denote σ e).1 = e.width →
      (denote σ e).1 = e.width ∧ 0 < 2 ^ e.width ∧
        (denote σ e).2.toNat = ((denote σ e).2.toNat + 0) % 2 ^ e.width := by
    intro e h
    exact ⟨h, Nat.two_pow_pos _, by simp [Nat.mod_eq_of_lt (toNat_lt_of_width h)]⟩
  fun_induction Memory.baseOffset e with
  | case1 width base constWidth value hguard inner offset hsplit ih =>
    obtain ⟨hv, hbw⟩ := hguard
    subst hv
    have hb := denote_offset_parts (σ := σ) "bvadd" (by decide) (by intros; simp [wordOp]) rfl h
    obtain ⟨h1, h2, h3⟩ := ih (by rw [hb, hbw])
    rw [hsplit] at h1 h2 h3
    simp only at h1 h2 h3 ⊢
    rw [hbw] at h1 h2 h3
    have hnat : (denote σ (.app "bvadd" constWidth [base, .const value])).2.toNat =
        ((denote σ base).2.toNat + value.toNat) % 2 ^ constWidth := by
      rw [denote_binary, denote_const]
      generalize denote σ base = d at hb
      obtain ⟨dw, x⟩ := d
      simp only at hb
      subst hb
      have hop : denoteBinary "bvadd" ⟨dw, x⟩ ⟨dw, value⟩ = ⟨dw, x + value⟩ := by simp [denoteBinary, wordOp]
      rw [hop]
      simp [BitVec.toNat_add]
    refine ⟨h1, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    simp only [Expr.width]
    rw [hnat, h3]
    simp [Nat.add_assoc]
  | case2 => exact hrefl h
  | case3 width base constWidth value hguard inner offset hsplit ih =>
    obtain ⟨hv, hbw⟩ := hguard
    subst hv
    have hb := denote_offset_parts (σ := σ) "bvsub" (by decide) (by intros; simp [wordOp]) rfl h
    obtain ⟨h1, h2, h3⟩ := ih (by rw [hb, hbw])
    rw [hsplit] at h1 h2 h3
    simp only at h1 h2 h3 ⊢
    rw [hbw] at h1 h2 h3
    have hnat : (denote σ (.app "bvsub" constWidth [base, .const value])).2.toNat =
        ((denote σ base).2.toNat + (2 ^ constWidth - value.toNat)) % 2 ^ constWidth := by
      rw [denote_binary, denote_const]
      generalize denote σ base = d at hb
      obtain ⟨dw, x⟩ := d
      simp only at hb
      subst hb
      have hop : denoteBinary "bvsub" ⟨dw, x⟩ ⟨dw, value⟩ = ⟨dw, x - value⟩ := by simp [denoteBinary, wordOp]
      rw [hop]
      simp [BitVec.toNat_sub, Nat.add_comm]
    refine ⟨h1, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    simp only [Expr.width]
    rw [hnat, h3]
    simp [Nat.add_assoc]
  | case4 => exact hrefl h
  | case5 => exact hrefl h

private theorem add_mod_ne {b x y m : Nat} (hx : x < m) (hy : y < m) (hne : x ≠ y) : (b + x) % m ≠ (b + y) % m := by
  intro he
  have hm : 0 < m := by omega
  have key : ∀ {p q : Nat}, p < q → q < m → (b + p) % m = (b + q) % m → False := by
    intro p q hpq hq e
    have hd : m ∣ (b + q) - (b + p) := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e.symm)
    have := Nat.le_of_dvd (by omega) hd
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key h hy he
  · exact key h hx he.symm

/-- The static resolution of addresses is sound: addresses it calls distinct never denote the same location,
which covers different constants and different offsets from one base. -/
theorem definitelyDistinct_sound (σ : Assignment) {a b : Expr} (ha : (denote σ a).1 = a.width)
    (hb : (denote σ b).1 = b.width) (h : Memory.definitelyDistinct a b = true) :
    sameBits (denote σ a) (denote σ b) = false := by
  have hgeneral : (a.width != b.width || ((Memory.baseOffset a).2 != (Memory.baseOffset b).2 &&
      Expr.structuralEq (Memory.baseOffset a).1 (Memory.baseOffset b).1)) = true →
      sameBits (denote σ a) (denote σ b) = false := by
    intro hg
    cases hs : sameBits (denote σ a) (denote σ b) with
    | false => rfl
    | true =>
      exfalso
      have he := sameBits_iff.mp hs
      have hw : a.width = b.width := by rw [← ha, ← hb, he]
      simp only [Bool.or_eq_true, bne_iff_ne, Bool.and_eq_true, ne_eq] at hg
      rcases hg with hg | ⟨hne, hbase⟩
      · exact hg hw
      · have hsame := structuralEq_iff.mp hbase
        obtain ⟨_, a2, a3⟩ := baseOffset_spec σ a ha
        obtain ⟨_, b2, b3⟩ := baseOffset_spec σ b hb
        rw [he, b3, hsame, ← hw] at a3
        rw [← hw] at b2
        exact add_mod_ne a2 b2 hne a3.symm
  cases a <;> cases b <;> first | exact hgeneral h | skip
  rw [denote_const, denote_const]
  simp [Memory.definitelyDistinct] at h
  simp only [sameBits, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  exact h

/-- Soundness under aliasing: for any assignment, a symbolic read denotes the byte the writes leave at
the location its address denotes. -/
theorem denote_readCells (σ : Assignment) {initial : Expr} {base : Bits → BitVec 8} {address : Expr}
    (ha : (denote σ address).1 = address.width) (cells : List (Expr × Expr)) (h : CellsSized σ cells)
    (hinitial : denote σ initial = ⟨8, base (denote σ address)⟩) :
    denote σ (Memory.readCells initial address cells) = ⟨8, byteMap σ base cells (denote σ address)⟩ := by
  induction cells with
  | nil => simpa [Memory.readCells, byteMap] using hinitial
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
        have := definitelyDistinct_sound σ (h cell (by simp)).2.2 ha hd
        simp only [this, ↓reduceIte, Bool.false_eq_true, ih']
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, denote_ite, isOne_denote_eq]
        cases hm : sameBits (denote σ cell.1) (denote σ address) with
        | true => simp only [↓reduceIte, hcell]
        | false => simp only [↓reduceIte, Bool.false_eq_true, ih']

/-- The memories whose stored bytes are all bytes, down through any conditional initial contents. -/
inductive MemorySized (σ : Assignment) : Bap.Symbolic.Memory → Prop where
  | plain (name cells) : CellsSized σ cells → MemorySized σ ⟨name, none, cells⟩
  | branch (name condition yes no cells) : MemorySized σ yes → MemorySized σ no → CellsSized σ cells →
      MemorySized σ ⟨name, some (condition, yes, no), cells⟩

theorem MemorySized.cellsSized {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : MemorySized σ memory) :
    CellsSized σ memory.cells := by
  cases h <;> assumption

theorem denote_readInitial (σ : Assignment) {memory : Bap.Symbolic.Memory} (h : MemorySized σ memory)
    {address : Expr} (ha : (denote σ address).1 = address.width) :
    denote σ (Memory.readInitial memory address) = ⟨8, baseByte σ memory (denote σ address)⟩ := by
  induction h with
  | plain name cells _ => simp [Memory.readInitial, baseByte, denote]
  | branch name condition yes no cells hy hn _ ihy ihn =>
    simp only [Memory.readInitial, baseByte, denote_ite]
    rw [denote_readCells σ ha _ hy.cellsSized ihy, denote_readCells σ ha _ hn.cellsSized ihn]
    split <;> rfl

theorem denote_readByte (σ : Assignment) {memory : Bap.Symbolic.Memory} {address : Expr}
    (ha : (denote σ address).1 = address.width) (h : MemorySized σ memory) :
    denote σ (memory.readByte address) = ⟨8, memoryByte σ memory (denote σ address)⟩ :=
  denote_readCells σ ha _ h.cellsSized (denote_readInitial σ h ha)

/-- A byte write updates the byte map at the one location its address denotes. -/
theorem byteMap_writeByte (σ : Assignment) (initial : Bits → BitVec 8) (memory : Bap.Symbolic.Memory)
    (address value : Expr) (target : Bits) :
    byteMap σ initial (memory.writeByte address value).cells target =
      if sameBits (denote σ address) target then byteOf σ value
      else byteMap σ initial memory.cells target := by
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

theorem baseByte_writeByte (σ : Assignment) (memory : Bap.Symbolic.Memory) (address value : Expr) :
    baseByte σ (memory.writeByte address value) = baseByte σ memory := by
  obtain ⟨name, branch, cells⟩ := memory
  cases branch with
  | none => rfl
  | some b => obtain ⟨_, _, _⟩ := b; rfl

theorem cellsSized_writeByte {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : CellsSized σ memory.cells)
    {address : Expr} (ha : (denote σ address).1 = address.width) {value : Expr} (hv : (denote σ value).1 = 8)
    (hw : value.width = 8) : CellsSized σ (memory.writeByte address value).cells := by
  intro cell hcell
  rcases List.mem_cons.mp hcell with rfl | hcell
  · exact ⟨hv, hw, ha⟩
  · exact h cell (List.mem_filter.mp hcell).1

theorem memorySized_writeByte {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : MemorySized σ memory)
    {address : Expr} (ha : (denote σ address).1 = address.width) {value : Expr} (hv : (denote σ value).1 = 8)
    (hw : value.width = 8) : MemorySized σ (memory.writeByte address value) := by
  have hc := cellsSized_writeByte h.cellsSized ha hv hw
  cases h with
  | plain name cells _ => exact .plain _ _ hc
  | branch name condition yes no cells hy hn _ => exact .branch _ _ _ _ _ hy hn hc

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

theorem width_offsetAddress (address : Expr) (offset : Nat) : (offsetAddress address offset).width = address.width := by
  unfold offsetAddress
  split
  · rfl
  · split <;> rfl

theorem fst_offsetAddress (σ : Assignment) (address : Expr) (offset : Nat)
    (h : (denote σ address).1 = address.width) :
    (denote σ (offsetAddress address offset)).1 = (offsetAddress address offset).width := by
  rw [denote_offsetAddress σ address offset h, width_offsetAddress]
  exact h

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

private theorem base_writePrefix (σ : Assignment) (memory : Bap.Symbolic.Memory) (address value : Expr)
    (endian : Endian) (size k : Nat) :
    baseByte σ (writePrefix memory address value endian size k) = baseByte σ memory := by
  induction k with
  | zero => rfl
  | succ k ih => rw [writePrefix_succ, writeStep, baseByte_writeByte, ih]

theorem memorySized_write {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : MemorySized σ memory)
    {address : Expr} (ha : (denote σ address).1 = address.width) (value : Expr) (endian : Endian) (size : Nat) :
    MemorySized σ (memory.write address value endian size) := by
  rw [write_eq_prefix]
  have : ∀ k, MemorySized σ (writePrefix memory address value endian size k) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [writePrefix_succ]
      exact memorySized_writeByte ih (fst_offsetAddress σ address k ha) (width_denote_byteAt ..) (by simp only [byteAt, Expr.width]; omega)
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
theorem memoryByte_write (σ : Assignment) (memory : Bap.Symbolic.Memory) (address value : Expr) (endian : Endian)
    (size : Nat) (h : (denote σ address).1 = address.width) (target : Bits) :
    memoryByte σ (memory.write address value endian size) target =
      modelWrite (memoryByte σ memory) (denote σ address) (denote σ value) endian size target := by
  rw [write_eq_prefix]
  have : ∀ k target, memoryByte σ (writePrefix memory address value endian size k) target =
      (List.range k).foldl (init := memoryByte σ memory) (fun bytes offset location =>
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
      simp only [memoryByte] at ih ⊢
      rw [writeStep, baseByte_writeByte, byteMap_writeByte, denote_offsetAddress σ address k h, byteOf_byteAt, ih]
      cases endian <;> rfl
  exact this size target

/-- The bytes of a read, most significant first, as a chain of concatenations. -/
def chainBytes : List Expr → Expr
  | [] => .const (BitVec.zero 0)
  | first :: rest => rest.foldl (fun result byte => .concat result byte) first

/-- What a read of `size` bytes denotes, when it has any bytes to read. -/
def readValue (memory : Bap.Symbolic.Memory) (address : Expr) (endian : Endian) (size : Nat) : Expr :=
  chainBytes (memory.readBytes address endian size)

theorem length_readBytes (memory : Bap.Symbolic.Memory) (address : Expr) (endian : Endian) (size : Nat) :
    (memory.readBytes address endian size).length = size := by
  simp only [Bap.Symbolic.Memory.readBytes]
  split <;> simp

/-- A read succeeds exactly when it has bytes to read. -/
theorem read_eq (memory : Bap.Symbolic.Memory) (address : Expr) (endian : Endian) {size : Nat} (hz : size ≠ 0) :
    memory.read address endian size = .ok (readValue memory address endian size) := by
  have hl := length_readBytes memory address endian size
  simp only [Bap.Symbolic.Memory.read, readValue]
  generalize memory.readBytes address endian size = bytes at hl ⊢
  cases bytes with
  | nil => exact absurd hl.symm hz
  | cons _ _ => rfl

/-- `Memory.read` with no bytes is rejected: no zero-width term ever exists. -/
theorem read_zero (memory : Bap.Symbolic.Memory) (address : Expr) (endian : Endian) :
    memory.read address endian 0 = .error "a load must have at least one byte" := by
  have hl := length_readBytes memory address endian 0
  simp only [Bap.Symbolic.Memory.read]
  generalize memory.readBytes address endian 0 = bytes at hl ⊢
  cases bytes with
  | nil => rfl
  | cons _ _ => simp at hl

theorem read_ok {memory : Bap.Symbolic.Memory} {address x : Expr} {endian : Endian} {size : Nat}
    (h : memory.read address endian size = .ok x) : size ≠ 0 ∧ x = readValue memory address endian size := by
  have hz : size ≠ 0 := by
    rintro rfl
    rw [read_zero] at h
    cases h
  rw [read_eq _ _ _ hz] at h
  cases h
  exact ⟨hz, rfl⟩

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
    (hcells : MemorySized σ memory) (h : (denote σ address).1 = address.width) :
    (denote σ (readValue memory address endian size)).1 = size * 8 ∧
      (denote σ (readValue memory address endian size)).2.toNat =
        modelRead (memoryByte σ memory) (denote σ address) endian size := by
  have hbyte : ∀ offset, denote σ (memory.readByte (offsetAddress address offset)) =
      ⟨8, memoryByte σ memory (offsetBits (denote σ address) offset)⟩ := by
    intro offset
    rw [denote_readByte σ (fst_offsetAddress σ address offset h) hcells, denote_offsetAddress σ address offset h]
  let exprs := (List.range size).map fun offset => memory.readByte (offsetAddress address offset)
  have hbytes : exprs.map (byteOf σ) =
      (List.range size).map fun offset =>
        memoryByte σ memory (offsetBits (denote σ address) offset) := by
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
  have hread : readValue memory address endian size =
      chainBytes (match endian with | .little => exprs.reverse | .big => exprs) := by
    unfold readValue Bap.Symbolic.Memory.readBytes
    cases endian
    · simp only [↓reduceIte, exprs]
    · simp only [↓reduceIte, reduceCtorEq, exprs]
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
    memoryByte σ memory ⟨w, address⟩

open Bap.Proofs.Core.MemoryLaws (PagesSized write_eq write_pagesSized readByte_write_frame image
  readByte_writeRegion_inside)
open_private_decls Bap.Proofs.Core Bap.Proofs.Core.MemoryLaws page_getBang toNat_add_ofNat
open_private_decls Bap.Core.Memory Bap Memory.byteAt

/-- The expressions and memories of a state are sized as their `width`s claim. -/
structure WellSized (σ : Assignment) (s : State) : Prop where
  envSized : ∀ entry ∈ s.env, (denote σ entry.2).1 = entry.2.width
  memoriesSized : ∀ entry ∈ s.memories, MemorySized σ entry.2

/-- A symbolic state stands for a concrete environment under an assignment. -/
structure Rel (σ : Assignment) (s : State) (env : Bil.Env) : Prop extends WellSized σ s where
  vars : ∀ var x w (v : BitVec w), isMemoryType var.typ = false → Assoc.get var s.env = some x →
    Bil.lookup env var = .ok (.bits v) → denote σ x = ⟨w, v⟩
  mems : ∀ var w (concrete : Bap.Memory w), isMemoryType var.typ = true →
    Bil.lookup env var = .ok (.memory concrete) → MemRel σ (memoryOf s var) concrete
  inputs : ∀ var w (v : BitVec w), isMemoryType var.typ = false → Assoc.get var s.env = none →
    Bil.lookup env var = .ok (.bits v) → denote σ (.var (inputName var) (typeWidth var.typ)) = ⟨w, v⟩
  pages : ∀ var w (concrete : Bap.Memory w), Bil.lookup env var = .ok (.memory concrete) → PagesSized concrete

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
    isMemoryType var.typ = false ∧ (Assoc.get var env = some x ∨
      Assoc.get var env = none ∧ x = .var (inputName var) (typeWidth var.typ) ∧ typeWidth var.typ ≠ 0) := by
  unfold lookup at h
  cases ht : var.typ <;> simp only [isMemoryType, true_and] <;> simp only [ht] at h
  case mem => cases h
  all_goals
    simp only [↓reduceIte, Bool.false_eq_true] at h
    split at h
    · next heq => cases h; exact .inl heq
    · next heq =>
      refine .inr ⟨heq, ?_⟩
      split at h
      · cases h
      · next hz =>
        cases h
        exact ⟨by simp only, by simpa only [ht] using hz⟩

theorem memorySized_memoryOf {σ : Assignment} {s : State} (h : WellSized σ s) (var : Bap.Var) :
    MemorySized σ (memoryOf s var) := by
  unfold memoryOf
  split
  · next memory heq => exact h.memoriesSized _ (get_mem heq)
  · exact .plain _ _ (fun _ hc => by cases hc)

private theorem binary_cases (op : Bil.BinOp) (left right : Expr) :
    binary op left right = binaryApp op left right ∨
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
theorem denote_binaryApp {σ : Assignment} (op : Bil.BinOp) {left right : Expr} {w : Nat} {x y : BitVec w}
    (hl : denote σ left = ⟨w, x⟩) (hr : denote σ right = ⟨w, y⟩) :
    denote σ (binaryApp op left right) = bilBinary op x y := by
  have app := @wordOp_app σ left right w x y hl hr
  cases op <;> simp [binaryApp, app, wordOp, bilBinary, Word.smod]

theorem fst_binaryApp (σ : Assignment) (op : Bil.BinOp) {left right : Expr}
    (hl : (denote σ left).1 = left.width) :
    (denote σ (binaryApp op left right)).1 = (binaryApp op left right).width := by
  have hpred : ∀ name k (l r : Expr), Expr.isPredicate name = true →
      (∀ {w} (x y : BitVec w), (wordOp name x y).1 = 1) → k = 1 →
      (denote σ (.app name k [l, r])).1 = k := by
    intro name k l r hp hw hk
    rw [denote_binary]
    unfold denoteBinary
    split
    · rw [hw, hk]
    · simp [hk, hp]
  have hplain : ∀ name (l r : Expr), Expr.isPredicate name = false → (denote σ l).1 = l.width →
      (∀ {w} (x y : BitVec w), (wordOp name x y).1 = w) →
      (denote σ (.app name l.width [l, r])).1 = l.width := by
    intro name l r hp hl hw
    rw [denote_binary]
    unfold denoteBinary
    split
    · rw [hw, hl]
    · simp [hp, hl]
  cases op
  all_goals first
    | exact hplain _ _ _ (by decide) hl (by intros; simp [wordOp])
    | exact hpred _ _ _ _ (by decide) (by intros; simp [wordOp]) rfl

private theorem fst_binary (σ : Assignment) (op : Bil.BinOp) {left right : Expr}
    (hl : (denote σ left).1 = left.width) :
    (denote σ (binary op left right)).1 = (binary op left right).width := by
  rcases binary_cases op left right with h | ⟨_, _, _, _, _, _, _, _, _, h⟩
  · rw [h]; exact fst_binaryApp σ op hl
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
    {initial : Expr} (hi : initial.width = 8) (address : Expr) : (Memory.readCells initial address cells).width = 8 := by
  induction cells with
  | nil => exact hi
  | cons cell rest ih =>
    have hc := h cell (by simp)
    have hr := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [Memory.readCells]
    repeat' split
    · exact hc
    · exact hr
    · exact hc

theorem width_readInitial {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : MemorySized σ memory) (address : Expr) :
    (Memory.readInitial memory address).width = 8 := by
  induction h with
  | plain name cells _ => rfl
  | branch name condition yes no cells hy _ _ ihy _ =>
    exact width_readCells (fun c hc => (hy.cellsSized c hc).2.1) ihy address

/-- A chain of bytes has their width. -/
theorem width_chainBytes {ordered : List Expr} (h : ∀ b ∈ ordered, b.width = 8) :
    (chainBytes ordered).width = ordered.length * 8 := by
  have hchain : ∀ (bytes : List Expr) (first : Expr), (∀ b ∈ bytes, b.width = 8) →
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
  cases ordered with
  | nil => rfl
  | cons first rest =>
    simp only [chainBytes]
    rw [hchain _ _ fun x hx => h x (by simp [hx]), h first (by simp)]
    simp only [List.length_cons]
    omega

private theorem width_readValue_of {memory : Bap.Symbolic.Memory} (h : ∀ a, (memory.readByte a).width = 8)
    (address : Expr) (endian : Endian) (size : Nat) : (readValue memory address endian size).width = size * 8 := by
  have hb : ∀ b ∈ memory.readBytes address endian size, b.width = 8 := by
    intro b hb
    simp only [Bap.Symbolic.Memory.readBytes] at hb
    split at hb <;> (try rw [List.mem_reverse] at hb) <;> obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb <;> exact h _
  rw [readValue, width_chainBytes hb, length_readBytes]

/-- Loads have the width the type checker assigns them. -/
theorem width_read {σ : Assignment} {memory : Bap.Symbolic.Memory} (h : MemorySized σ memory) (address : Expr)
    (endian : Endian) (size : Nat) : (readValue memory address endian size).width = size * 8 :=
  width_readValue_of (fun _ => width_readCells (fun c hc => (h.cellsSized c hc).2.1) (width_readInitial h _) _)
    address endian size

private theorem wellSized_bind {σ : Assignment} {s : State} (h : WellSized σ s) (var : Bap.Var) {x : Expr}
    (hx : (denote σ x).1 = x.width) : WellSized σ { s with env := (var, x) :: s.env } :=
  ⟨fun entry he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hx
      · exact h.envSized entry he,
    h.memoriesSized⟩

private theorem wellSized_bindMemory {σ : Assignment} {s : State} (h : WellSized σ s) (var : Bap.Var)
    {m : Bap.Symbolic.Memory} (hm : MemorySized σ m) : WellSized σ { s with memories := (var, m) :: s.memories } :=
  ⟨h.envSized, fun entry he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hm
      · exact h.memoriesSized entry he⟩

private theorem memoryIte_sized {σ : Assignment} {c : Expr} {yes no result : Bap.Symbolic.Memory}
    (hy : MemorySized σ yes) (hn : MemorySized σ no)
    (h : (match c.knownCondition with
      | some true => Except.ok yes
      | some false => .ok no
      | none => .ok { name := yes.name, branch := some (c, yes, no) } : Except String Bap.Symbolic.Memory) = .ok result) :
    MemorySized σ result := by
  split at h
  · cases h; exact hy
  · cases h; exact hn
  · cases h; exact .branch _ _ _ _ _ hy hn (fun _ hc => by cases hc)

theorem sized_eval (σ : Assignment) (e : Bil.Exp) :
    (∀ {s : State} {x : Expr}, WellSized σ s → evalExp s e = .ok x → (denote σ x).1 = x.width) ∧
      (∀ {s : State} {memory : Bap.Symbolic.Memory}, WellSized σ s → evalMemory s e = .ok memory →
        MemorySized σ memory) := by
  induction e with
  | int value =>
    refine ⟨fun _ h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp] at h
    split at h
    · cases h
    · cases h; simp [Expr.width]
  | var var =>
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp] at h
      rcases (lookup_ok h).2 with hg | ⟨_, rfl, _⟩
      · exact hs.envSized _ (get_mem hg)
      · simp [Expr.width]
    · simp only [evalMemory] at h
      split at h
      · cases h
        exact memorySized_memoryOf hs var
      · cases h
  | load memory address endian size ihm iha =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨m, hm, a, ha, h⟩ := h
    cases (read_ok h).2
    have hc := ihm.2 hs hm
    rw [(denote_read σ m a endian size hc (iha.1 hs ha)).1, width_read hc]
  | store memory address value endian size ihm iha ihv =>
    refine ⟨fun _ h => by simp [evalExp] at h, fun hs h => ?_⟩
    simp only [evalMemory, bind_ok] at h
    obtain ⟨m, hm, a, ha, v, _, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact memorySized_write (ihm.2 hs hm) (iha.1 hs ha) _ _ _
  | bin op left right ihl ihr =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hrr, h⟩ := h
    split at h
    · cases h
    · cases h
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
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp, bind_ok] at h
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
    · simp only [evalMemory, bind_ok] at h
      obtain ⟨c, _, y, hy, n, hn, h⟩ := h
      split at h
      · cases h
      · exact memoryIte_sized (ihy.2 hs hy) (ihn.2 hs hn) h
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
    refine ⟨fun _ h => ?_, fun _ h => ?_⟩
    · simp only [evalExp] at h
      split at h
      · cases h
      · cases h; simp [Expr.width]
    · simp only [evalMemory] at h
      cases h
      exact .plain _ _ (fun _ hc => by cases hc)

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

private theorem pages_bind {env : Bil.Env} {var : Bap.Var} {value : Value}
    (h : ∀ var w (concrete : Bap.Memory w), Bil.lookup env var = .ok (.memory concrete) → PagesSized concrete)
    (hv : ∀ {w} {c : Bap.Memory w}, value = .memory c → PagesSized c) :
    ∀ var' w (concrete : Bap.Memory w), Bil.lookup (Bil.bind env var value) var' = .ok (.memory concrete) →
      PagesSized concrete := by
  intro var' w c hl
  by_cases he : var' = var
  · subst he
    rw [find_bind_same] at hl
    cases hl
    exact hv rfl
  · rw [lookup_bind_ne _ _ he] at hl
    exact h _ _ _ hl

/-- Binding a bitvector variable keeps a state related to its concrete environment. -/
theorem rel_bind {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) {var : Bap.Var} {x : Expr}
    {value : Value} (hmem : isMemoryType var.typ = false) (hx : (denote σ x).1 = x.width)
    (hv : ∀ {w} {v : BitVec w}, value = .bits v → denote σ x = ⟨w, v⟩)
    (hp : ∀ {w} {c : Bap.Memory w}, value = .memory c → PagesSized c) :
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
  inputs := by
    intro var' w v hm hg hl
    by_cases he : var' = var
    · subst he
      rw [get_cons_same] at hg
      cases hg
    · rw [get_cons_ne _ _ he] at hg
      rw [lookup_bind_ne _ _ he] at hl
      exact h.inputs _ _ _ hm hg hl
  pages := pages_bind h.pages hp

/-- Binding a memory variable keeps a state related to its concrete environment. -/
theorem rel_bindMemory {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) {var : Bap.Var}
    {m : Bap.Symbolic.Memory} {value : Value} (hmem : isMemoryType var.typ = true) (hm : MemorySized σ m)
    (hv : ∀ {w} {c : Bap.Memory w}, value = .memory c → MemRel σ m c)
    (hp : ∀ {w} {c : Bap.Memory w}, value = .memory c → PagesSized c) :
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
  inputs := by
    intro var' w v ht hg hl
    have he : var' ≠ var := by
      rintro rfl
      rw [ht] at hmem; cases hmem
    rw [lookup_bind_ne _ _ he] at hl
    exact h.inputs _ _ _ ht hg hl
  pages := pages_bind h.pages hp

/-! ### Unknowns: an oracle semantics

The concrete evaluator has no value for an `unknown`. Here one comes from an oracle: any way of resolving them is a
run. `oEval` is `Bil.evalExp` but for that, and `oExecStmt` is `Bil.execStmt` but for naming each `unknown` it reaches
by the count of those drawn so far, as the executor does, so that each draw is a value of its own. -/

/-- The value an oracle gives each `unknown`, by its name; it may leave a memory undefined. -/
structure Oracle where
  bits : String → (width : Nat) → BitVec width
  memory : String → (addressWidth : Nat) → Option (Bap.Memory addressWidth)

/-- The value of an `unknown` of a type, of that type. -/
def Oracle.draw (o : Oracle) (message : String) : Typ → Value
  | .mem addressWidth _ => (o.memory message addressWidth).elim .undefined fun memory => .memory memory
  | typ => .bits (o.bits message (typeWidth typ))

def oEval (o : Oracle) (env : Bil.Env) : Bil.Exp → Except String Value
  | .int value => .ok (.bits value)
  | .var var => Bil.lookup env var
  | .load memory address endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← oEval o env memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← oEval o env address)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      .ok (.bits (Bap.Memory.read memory address endian size))
    else
      .error "address width does not match memory"
  | .store memory address value endian size => do
    let ⟨addressWidth, memory⟩ ← expectMemory (← oEval o env memory)
    let ⟨actualWidth, address⟩ ← Value.asBits (← oEval o env address)
    let value ← Value.asBits (← oEval o env value)
    if h : actualWidth = addressWidth then
      let address : BitVec addressWidth := h ▸ address
      let updated ← Bap.Memory.write memory address value.2 endian size
      .ok (.memory updated)
    else
      .error "address width does not match memory"
  | .bin op left right => do
    let left ← Value.asBits (← oEval o env left)
    let right ← Value.asBits (← oEval o env right)
    Bil.evalBin op left right
  | .un op value => do
    .ok (evalUn op (← Value.asBits (← oEval o env value)))
  | .cast kind width value => do
    let value ← Value.asBits (← oEval o env value)
    match kind with
    | .low => .ok (.bits (Word.low width value.2))
    | .unsigned => .ok (.bits (Word.unsigned width value.2))
    | .signed => .ok (.bits (Word.signed width value.2))
    | .high => do
      let result ← Word.high width value.2
      .ok (.bits result)
  | .letIn var value body => do
    let value ← oEval o env value
    oEval o (Bil.bind env var value) body
  | .ite condition yes no => do
    let ⟨width, condition⟩ ← Value.asBits (← oEval o env condition)
    if h : width = 1 then
      let condition : BitVec 1 := h ▸ condition
      if condition = 1 then oEval o env yes else oEval o env no
    else
      .error "condition must be one bit"
  | .extract high low value => do
    let value ← Value.asBits (← oEval o env value)
    let result ← Word.extract high low value.2
    .ok (.bits result)
  | .concat left right => do
    let left ← Value.asBits (← oEval o env left)
    let right ← Value.asBits (← oEval o env right)
    .ok (.bits (Word.concat left.2 right.2))
  | .unknown message typ => .ok (o.draw message typ)

/-- An oracle's values are an assignment's values for the names of the unknowns. -/
structure Agrees (σ : Assignment) (o : Oracle) : Prop where
  bits : ∀ message width, σ.var (unknownName message) width = o.bits message width
  memory : ∀ message w (c : Bap.Memory w), o.memory message w = some c →
    MemRel σ { name := unknownName message } c ∧ PagesSized c

/-- The oracle of an assignment, which leaves the memories undefined: no concrete memory need have its bytes. -/
def Oracle.ofAssignment (σ : Assignment) : Oracle where
  bits message width := σ.var (unknownName message) width
  memory _ _ := none

theorem agrees_ofAssignment (σ : Assignment) : Agrees σ (Oracle.ofAssignment σ) :=
  ⟨fun _ _ => rfl, fun _ _ _ h => by cases h⟩

/-- Memories in the concrete evaluator keep their pages whole: the side condition of the `Bap.Memory` laws is
an invariant of evaluation. -/
theorem pages_evalExp {o : Oracle} (ho : ∀ message w (c : Bap.Memory w), o.memory message w = some c → PagesSized c)
    (e : Bil.Exp) : ∀ {env : Bil.Env} {w : Nat} {c : Bap.Memory w},
    (∀ var w (concrete : Bap.Memory w), Bil.lookup env var = .ok (.memory concrete) → PagesSized concrete) →
    oEval o env e = .ok (.memory c) → PagesSized c := by
  induction e with
  | var var => intro env w c h hc; exact h var w c hc
  | store memory address value endian size ihm =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨mv, hmv, ⟨mw, cm⟩, hexp, av, hav, ⟨aw, addr⟩, hbits, vv, hvv, ⟨vw, val⟩, hvbits, hc⟩ := hc
    cases mv <;> simp only [expectMemory, reduceCtorEq] at hexp
    cases hexp
    simp only at hc
    by_cases hw : aw = mw
    · subst hw
      simp only [↓reduceDIte] at hc
      obtain ⟨updated, hu, hc⟩ := bind_ok.mp hc
      cases hc
      exact write_pagesSized (ihm h hmv) hu
    · simp [hw] at hc
  | letIn var value body ihv ihb =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨cv, hcv, hc⟩ := hc
    exact ihb (pages_bind h (fun he => ihv h (he ▸ hcv))) hc
  | ite condition yes no _ ihy ihn =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
    simp only at hc
    by_cases hw : cw = 1
    · subst hw
      simp only [↓reduceDIte] at hc
      split at hc
      · exact ihy h hc
      · exact ihn h hc
    · simp [hw] at hc
  | int value => intro env w c h hc; simp [oEval] at hc
  | load memory address endian size =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨_, _, _, _, _, _, ⟨aw, _⟩, _, hc⟩ := hc
    simp only at hc
    split at hc <;> cases hc
  | bin op left right =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨_, _, ⟨lw, lv⟩, _, _, _, ⟨rw, rv⟩, _, hc⟩ := hc
    by_cases hwidth : lw = rw
    · subst hwidth
      obtain ⟨v', hv', _⟩ := evalBin_same op lv rv
      rw [hv'] at hc
      cases hc
    · simp [Bil.evalBin, hwidth] at hc
  | un op value =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨_, _, ⟨_, _⟩, _, hc⟩ := hc
    cases op <;> simp only [evalUn, Except.ok.injEq] at hc <;> cases hc
  | cast kind width value =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨_, _, ⟨_, _⟩, _, hc⟩ := hc
    cases kind
    case high =>
      obtain ⟨_, _, hc⟩ := bind_ok.mp hc
      cases hc
    all_goals cases hc
  | extract high low value =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨_, _, ⟨_, _⟩, _, _, _, hc⟩ := hc
    cases hc
  | concat left right =>
    intro env w c h hc
    simp only [oEval, bind_ok] at hc
    obtain ⟨_, _, ⟨_, _⟩, _, _, _, ⟨_, _⟩, _, hc⟩ := hc
    cases hc
  | unknown message typ =>
    intro env w c h hc
    simp only [oEval, Except.ok.injEq] at hc
    cases typ <;> simp only [Oracle.draw, reduceCtorEq] at hc
    next addressWidth _ =>
    cases hm : o.memory message addressWidth with
    | none => simp [hm] at hc
    | some m =>
      simp only [hm, Option.elim_some, Value.memory.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      cases eq_of_heq hc
      exact ho _ _ _ hm

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

/-- A write leaves a location alone that none of its bytes touch. -/
theorem modelWrite_outside (bytes : ByteMap) (target value : Bits) (endian : Endian) {size : Nat} {location : Bits}
    (h : ∀ k < size, sameBits (offsetBits target k) location = false) :
    modelWrite bytes target value endian size location = bytes location := by
  simp only [modelWrite]
  have : ∀ n, n ≤ size → (List.range n).foldl (init := bytes) (fun bytes offset location =>
        if sameBits (offsetBits target offset) location then
          valueByte value (match endian with | .little => offset | .big => size - 1 - offset)
        else bytes location) location = bytes location := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [modelWrite_succ]
      simp only [h n (by omega), Bool.false_eq_true, ↓reduceIte]
      exact ih (by omega)
  exact this size (Nat.le_refl _)

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

/-- The store law: the real `Bap.Memory.write` has the bytes of the symbolic model, wrapping included, as long
as its pages are whole, which `pages_evalExp` keeps, and the store does not overlap itself, which the executor
rejects. -/
theorem memRel_write {σ : Assignment} {memory : Bap.Symbolic.Memory} {w vw : Nat} {concrete updated : Bap.Memory w}
    {a x : Expr} {address : BitVec w} {value : BitVec vw} {endian : Endian} {size : Nat}
    (hrel : MemRel σ memory concrete) (hpages : PagesSized concrete) (hda : denote σ a = ⟨w, address⟩)
    (hwa : a.width = w) (hdx : denote σ x = ⟨vw, value⟩) (hsize : size ≤ 2 ^ w)
    (hu : Bap.Memory.write concrete address value endian size = .ok updated) :
    MemRel σ (memory.write a x endian size) updated := by
  intro location
  rw [memoryByte_write σ memory a x endian size (by rw [hda, hwa]), hda, hdx]
  by_cases hin : ∃ k, k < size ∧ location = address + BitVec.ofNat w k
  · obtain ⟨k, hk, rfl⟩ := hin
    have hs : size * 8 = vw := by
      by_cases hne : size * 8 = vw
      · exact hne
      · simp [Bap.Memory.write, hne] at hu
    rw [write_eq hs endian] at hu
    simp only [Except.ok.injEq] at hu
    subst hu
    have himage : (image value endian size).length = size := by simp [image]
    have hdata : (ByteArray.mk (image value endian size).toArray).size = size := by
      show (image value endian size).toArray.size = size
      simp [himage]
    have hbyte := readByte_writeRegion_inside hpages address.toNat (ByteArray.mk (image value endian size).toArray)
      (by rw [hdata]; exact hsize) (j := k) (by rw [hdata]; exact hk) (address + BitVec.ofNat w k)
      (toNat_add_ofNat address k)
    rw [hbyte, page_getBang]
    have hmodel := modelWrite_offset (memoryByte σ memory) ⟨w, address⟩ ⟨vw, value⟩ endian (size := size) (k := k) hsize hk
    simp only [offsetBits] at hmodel
    rw [hmodel]
    show ((image value endian size).toArray[k]!).toBitVec = _
    rw [getElem!_pos _ k (by simpa [himage] using hk)]
    apply BitVec.eq_of_toNat_eq
    cases endian <;> simp [image, Memory.byteAt, valueByte, Nat.mul_comm 8]
  · have hne : ∀ k, k < size → location ≠ address + BitVec.ofNat w k := by
      intro k hk he
      exact hin ⟨k, hk, he⟩
    rw [readByte_write_frame hpages hu hne, hrel location, modelWrite_outside]
    intro k hk
    cases hb : sameBits (offsetBits ⟨w, address⟩ k) ⟨w, location⟩ with
    | false => rfl
    | true =>
      have e := sameBits_iff.mp hb
      simp only [offsetBits, Sigma.mk.injEq, heq_eq_eq, true_and] at e
      exact absurd e.symm (hne k hk)

private theorem fold_toBitVec (bytes : List UInt8) :
    bytes.foldl (fun result byte => result * 256 + byte.toNat) 0 =
      (bytes.map UInt8.toBitVec).foldl (fun result byte => result * 256 + byte.toNat) 0 := by
  rw [List.foldl_map]
  rfl

/-- A load through related memories denotes the concrete load. -/
theorem denote_read_concrete {σ : Assignment} {memory : Bap.Symbolic.Memory} {w : Nat} {concrete : Bap.Memory w}
    (hrel : MemRel σ memory concrete) (hcells : MemorySized σ memory) {address : Expr} {a : BitVec w}
    (hd : denote σ address = ⟨w, a⟩) (hw : address.width = w) (endian : Endian) (size : Nat) :
    denote σ (readValue memory address endian size) = ⟨size * 8, Bap.Memory.read concrete a endian size⟩ := by
  obtain ⟨h1, h2⟩ := denote_read σ memory address endian size hcells (by rw [hd, hw])
  refine bits_ext h1 ?_
  rw [h2, hd]
  have hbound := toNat_lt_of_width h1
  rw [h2, hd] at hbound
  have hbytes : ((List.range size).map fun offset =>
      Bap.Memory.readByte concrete (a + BitVec.ofNat w offset)).map UInt8.toBitVec =
      (List.range size).map fun offset =>
        memoryByte σ memory (offsetBits ⟨w, a⟩ offset) := by
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
      rw [he, denote_binaryApp op hl hr]
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

/-- Soundness of expression evaluation: under any assignment related to the concrete environment, the
symbolic value of an expression denotes its concrete value. -/
theorem evalExp_sound (σ : Assignment) {o : Oracle} (ho : Agrees σ o) (e : Bil.Exp) :
    (∀ {s : State} {env : Bil.Env} {x : Expr} {w : Nat} {v : BitVec w}, Rel σ s env → evalExp s e = .ok x →
      oEval o env e = .ok (.bits v) → denote σ x = ⟨w, v⟩) ∧
    (∀ {s : State} {env : Bil.Env} {memory : Bap.Symbolic.Memory} {w : Nat} {c : Bap.Memory w}, Rel σ s env →
      evalMemory s e = .ok memory → oEval o env e = .ok (.memory c) → MemRel σ memory c) := by
  have hpages := fun message w c h => (ho.memory message w c h).2
  induction e with
  | int value =>
    refine ⟨fun _ h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp] at h
    split at h
    · cases h
    · cases h
      simp only [oEval, Except.ok.injEq] at hc
      cases hc
      simp
  | var var =>
    refine ⟨fun hr h hc => ?_, fun hr h hc => ?_⟩
    · simp only [evalExp] at h
      obtain ⟨hm, hg⟩ := lookup_ok h
      simp only [oEval] at hc
      rcases hg with hg | ⟨hg, rfl, _⟩
      · exact hr.vars _ _ _ _ hm hg hc
      · exact hr.inputs _ _ _ hm hg hc
    · simp only [evalMemory] at h
      split at h
      · next hm =>
        cases h
        simp only [oEval] at hc
        exact hr.mems _ _ _ hm hc
      · cases h
  | load memory address endian size ihm iha =>
    refine ⟨@fun s env x w v hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨m, hm, a, ha, h⟩ := h
    cases (read_ok h).2
    simp only [oEval, bind_ok] at hc
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
      have hma := iha.1 hr ha hav
      have hsa' := (sized_eval σ address).1 hr.toWellSized ha
      rw [hma] at hsa'
      exact denote_read_concrete (ihm.2 hr hm hmv) ((sized_eval σ memory).2 hr.toWellSized hm) hma hsa'.symm _ _
    · simp [hw] at hc
  | store memory address value endian size ihm iha ihv =>
    refine ⟨fun _ h _ => by simp [evalExp] at h, fun hr h hc => ?_⟩
    simp only [evalMemory, bind_ok] at h
    obtain ⟨m, hm, a, ha, x, hx, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · next hfit =>
          cases h
          simp only [oEval, bind_ok] at hc
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
            have hma := iha.1 hr ha hav
            have hmx := ihv.1 hr hx hvv
            have hsa := (sized_eval σ address).1 hr.toWellSized ha
            rw [hma] at hsa
            have hsa' := hsa.symm
            simp only at hsa'
            rw [hsa'] at hfit
            exact memRel_write (ihm.2 hr hm hmv) (pages_evalExp hpages memory hr.pages hmv) hma hsa' hmx
              (by simpa using hfit) hu
          · simp [hw] at hc
  | bin op left right ihl ihr =>
    refine ⟨fun hr' h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hrr, h⟩ := h
    split at h
    · cases h
    cases h
    simp only [oEval, bind_ok] at hc
    obtain ⟨lv, hlv, ⟨lw, lb⟩, hlb, rv, hrv, ⟨rw, rb⟩, hrb, hc⟩ := hc
    cases lv <;> simp only [Value.asBits, reduceCtorEq] at hlb
    cases hlb
    cases rv <;> simp only [Value.asBits, reduceCtorEq] at hrb
    cases hrb
    have hdl := ihl.1 hr' hl hlv
    have hdr := ihr.1 hr' hrr hrv
    have hwl := (sized_eval σ left).1 hr'.toWellSized hl
    have hwr := (sized_eval σ right).1 hr'.toWellSized hrr
    rw [hdl] at hwl
    rw [hdr] at hwr
    exact denote_binary_sound hdl hdr hwl.symm hwr.symm hc
  | un op value ih =>
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    cases h
    simp only [oEval, bind_ok] at hc
    obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
    cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
    cases hcb
    have hdx := ih.1 hr hx hcv
    have hunary : ∀ name k, denote σ (.app name k [x]) = denoteUnary name k (denote σ x) := by
      intro name k; simp [denote]
    rw [hunary, hdx]
    cases op <;> simp only [evalUn, Except.ok.injEq] at hc <;> cases hc <;> simp [denoteUnary]
  | cast kind width value ih =>
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    simp only [oEval, bind_ok] at hc
    obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
    cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
    cases hcb
    have hdx := ih.1 hr hx hcv
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
    have bits : ∀ {s : State} {env : Bil.Env} {x : Expr} {cv : Value}, Rel σ s env →
        isMemoryType var.typ = false → evalExp s value = .ok x → oEval o env value = .ok cv →
        Rel σ { s with env := (var, x) :: s.env } (Bil.bind env var cv) := by
      intro s env x cv hr hmem hx hcv
      exact rel_bind hr hmem ((sized_eval σ value).1 hr.toWellSized hx)
        (fun he => ihv.1 hr hx (he ▸ hcv)) (fun he => pages_evalExp hpages value hr.pages (he ▸ hcv))
    have mem : ∀ {s : State} {env : Bil.Env} {m : Bap.Symbolic.Memory} {cv : Value}, Rel σ s env →
        isMemoryType var.typ = true → evalMemory s value = .ok m → oEval o env value = .ok cv →
        Rel σ { s with memories := (var, m) :: s.memories } (Bil.bind env var cv) := by
      intro s env m cv hr hmem hm hcv
      exact rel_bindMemory hr hmem ((sized_eval σ value).2 hr.toWellSized hm)
        (fun he => ihv.2 hr hm (he ▸ hcv)) (fun he => pages_evalExp hpages value hr.pages (he ▸ hcv))
    refine ⟨fun hr h hc => ?_, fun hr h hc => ?_⟩
    · simp only [evalExp] at h
      simp only [oEval, bind_ok] at hc
      obtain ⟨cv, hcv, hc⟩ := hc
      split at h
      · next hm =>
        obtain ⟨m, hm', h⟩ := bind_ok.mp h
        exact ihb.1 (mem hr hm hm' hcv) h hc
      · next hm =>
        obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact ihb.1 (bits hr (by simpa using hm) hx hcv) h hc
    · simp only [evalMemory] at h
      simp only [oEval, bind_ok] at hc
      obtain ⟨cv, hcv, hc⟩ := hc
      split at h
      · next hm =>
        obtain ⟨m, hm', h⟩ := bind_ok.mp h
        exact ihb.2 (mem hr hm hm' hcv) h hc
      · next hm =>
        obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact ihb.2 (bits hr (by simpa using hm) hx hcv) h hc
  | ite condition yes no ihc ihy ihn =>
    refine ⟨fun hr h hc => ?_, fun hr h hc => ?_⟩
    rotate_left
    · simp only [evalMemory, bind_ok] at h
      obtain ⟨c, hcond, y, hy, n, hn, h⟩ := h
      split at h
      · cases h
      · next hcw =>
        simp only [oEval, bind_ok] at hc
        obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
        cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
        cases hcb
        simp only at hc
        by_cases hw : cw = 1
        · subst hw
          simp only [↓reduceDIte] at hc
          have hdc := ihc.1 hr hcond hcv
          have hsy := (sized_eval σ yes).2 hr.toWellSized hy
          have hsn := (sized_eval σ no).2 hr.toWellSized hn
          by_cases h1 : cb = 1
          · rw [ite_eq_left h1] at hc
            have hrel := ihy.2 hr hy hc
            have hone : isOne (denote σ c) = true := by rw [hdc]; exact (isOne_one_iff cb).mpr h1
            split at h
            · cases h; exact hrel
            · next hk =>
              have := (known_sound hk hdc).mp h1
              cases this
            · cases h
              intro location
              rw [hrel location]
              simp [memoryByte, baseByte, byteMap, hone]
          · rw [ite_eq_right h1] at hc
            have hrel := ihn.2 hr hn hc
            have hone : isOne (denote σ c) = false := by
              rw [hdc]
              cases he : isOne ⟨1, cb⟩ with
              | false => rfl
              | true => exact absurd ((isOne_one_iff cb).mp he) h1
            split at h
            · next hk =>
              exact absurd ((known_sound hk hdc).mpr rfl) h1
            · cases h; exact hrel
            · cases h
              intro location
              rw [hrel location]
              simp [memoryByte, baseByte, byteMap, hone]
        · simp [hw] at hc
    simp only [evalExp, bind_ok] at h
    obtain ⟨c, hcond, y, hy, n, hn, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [oEval, bind_ok] at hc
        obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, hc⟩ := hc
        cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
        cases hcb
        simp only at hc
        by_cases hw : cw = 1
        · subst hw
          have hdc := ihc.1 hr hcond hcv
          rw [denote_ite, hdc]
          simp only [↓reduceDIte] at hc
          by_cases h1 : cb = 1
          · rw [ite_eq_left h1] at hc
            rw [ite_eq_left ((isOne_one_iff cb).mpr h1)]
            exact ihy.1 hr hy hc
          · rw [ite_eq_right h1] at hc
            rw [ite_eq_right (fun e => h1 ((isOne_one_iff cb).mp e))]
            exact ihn.1 hr hn hc
        · simp [hw] at hc
  | extract high low value ih =>
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        simp only [oEval, bind_ok] at hc
        obtain ⟨cv, hcv, ⟨cw, cb⟩, hcb, res, hres, hc⟩ := hc
        cases cv <;> simp only [Value.asBits, reduceCtorEq] at hcb
        cases hcb
        cases hc
        have hdx := ih.1 hr hx hcv
        rw [denote_extract_of hdx]
        simp only [Word.extract] at hres
        split at hres
        · cases hres
        · split at hres
          · cases hres
          · cases hres; rfl
  | concat left right ihl ihr =>
    refine ⟨fun hr h hc => ?_, fun _ h _ => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hrr, h⟩ := h
    cases h
    simp only [oEval, bind_ok] at hc
    obtain ⟨lv, hlv, ⟨lw, lb⟩, hlb, rv, hrv, ⟨rw, rb⟩, hrb, hc⟩ := hc
    cases lv <;> simp only [Value.asBits, reduceCtorEq] at hlb
    cases hlb
    cases rv <;> simp only [Value.asBits, reduceCtorEq] at hrb
    cases hrb
    cases hc
    have hdl := ihl.1 hr hl hlv
    have hdr := ihr.1 hr hrr hrv
    simp only [denote]
    rw [hdl, hdr]
    rfl
  | unknown message typ =>
    refine ⟨fun _ h hc => ?_, fun _ h hc => ?_⟩
    · simp only [evalExp] at h
      split at h
      · cases h
      · cases h
        simp only [oEval, Except.ok.injEq] at hc
        cases typ
        case mem aw _ _ =>
          cases hm : o.memory message aw <;> simp [Oracle.draw, hm] at hc
        all_goals
          simp only [Oracle.draw, Value.bits.injEq] at hc
          obtain ⟨rfl, hc⟩ := hc
          cases eq_of_heq hc
          rw [denote_var, ho.bits]
    · simp only [evalMemory] at h
      cases h
      simp only [oEval, Except.ok.injEq] at hc
      cases typ <;> simp only [Oracle.draw, reduceCtorEq] at hc
      next aw vw =>
      cases hm : o.memory message aw with
      | none => simp [hm] at hc
      | some m =>
        simp only [hm, Option.elim_some, Value.memory.injEq] at hc
        obtain ⟨rfl, hc⟩ := hc
        cases eq_of_heq hc
        exact (ho.memory _ _ _ hm).1

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

/-- A concrete state: an environment, and how many unknowns have been drawn. -/
structure OState where
  env : Bil.Env := []
  unknowns : Nat := 0

mutual
  /-- `Bil.execStmt` with the unknowns of each expression it runs named as the executor names them, and given their
  values by an oracle. -/
  def oExecStmt (o : Oracle) (fuel : Nat) (state : OState) (stmt : Bil.Stmt) : Except String (OState × Bil.Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match stmt with
      | .move var value => do
        let result ← oEval o state.env (freshenUnknowns state.unknowns value).1
        .ok ({ env := Bil.bind state.env var result, unknowns := (freshenUnknowns state.unknowns value).2 }, .normal)
      | .jmp target => do
        let result ← Value.asBits (← oEval o state.env (freshenUnknowns state.unknowns target).1)
        .ok ({ state with unknowns := (freshenUnknowns state.unknowns target).2 }, .jump result.2)
      | .special message => .ok (state, .special message)
      | .cpuExn number => .ok (state, .cpuExn number)
      | .ifElse condition yes no => do
        let ⟨width, value⟩ ← Value.asBits (← oEval o state.env (freshenUnknowns state.unknowns condition).1)
        if h : width = 1 then
          let value : BitVec 1 := h ▸ value
          oExecProgram o fuel { state with unknowns := (freshenUnknowns state.unknowns condition).2 }
            (if value = 1 then yes else no)
        else
          .error "condition must be one bit"
      | .while condition body => do
        let ⟨width, value⟩ ← Value.asBits (← oEval o state.env (freshenUnknowns state.unknowns condition).1)
        if h : width = 1 then
          let value : BitVec 1 := h ▸ value
          let drawn := { state with unknowns := (freshenUnknowns state.unknowns condition).2 }
          if value = 1 then
            let (next, effect) ← oExecProgram o fuel drawn body
            match effect with
            | .normal => oExecStmt o fuel next (.while condition body)
            | other => .ok (next, other)
          else
            .ok (drawn, .normal)
        else
          .error "condition must be one bit"

  def oExecProgram (o : Oracle) (fuel : Nat) (state : OState) (program : Bil.Program) :
      Except String (OState × Bil.Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match program with
      | [] => .ok (state, .normal)
      | stmt :: rest => do
        let (next, effect) ← oExecStmt o fuel state stmt
        match effect with
        | .normal => oExecProgram o fuel next rest
        | other => .ok (next, other)
end

/-- An expression evaluated without an oracle needs none, whatever its unknowns are named. -/
theorem oEval_of_evalExp (o : Oracle) (e : Bil.Exp) : ∀ (next : Nat) {env : Bil.Env} {value : Value},
    Bil.evalExp env e = .ok value → oEval o env (freshenUnknowns next e).1 = .ok value := by
  induction e with
  | int value => intro _ _ _ h; exact h
  | var var => intro _ _ _ h; exact h
  | unknown message typ => intro _ _ _ h; simp [Bil.evalExp] at h
  | load memory address endian size ihm iha =>
    intro next env value h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨mv, hm, x, hx, av, ha, y, hy, h⟩ := h
    show oEval o env (.load (freshenUnknowns next memory).1 (freshenUnknowns _ address).1 endian size) = _
    simp only [oEval, bind_ok]
    exact ⟨mv, ihm _ hm, x, hx, av, iha _ ha, y, hy, h⟩
  | store memory address value endian size ihm iha ihv =>
    intro next env result h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨mv, hm, x, hx, av, ha, y, hy, vv, hv, z, hz, h⟩ := h
    show oEval o env (.store (freshenUnknowns next memory).1 (freshenUnknowns _ address).1
      (freshenUnknowns _ value).1 endian size) = _
    simp only [oEval, bind_ok]
    exact ⟨mv, ihm _ hm, x, hx, av, iha _ ha, y, hy, vv, ihv _ hv, z, hz, h⟩
  | bin op left right ihl ihr =>
    intro next env value h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨lv, hl, x, hx, rv, hr, y, hy, h⟩ := h
    show oEval o env (.bin op (freshenUnknowns next left).1 (freshenUnknowns _ right).1) = _
    simp only [oEval, bind_ok]
    exact ⟨lv, ihl _ hl, x, hx, rv, ihr _ hr, y, hy, h⟩
  | un op value ih =>
    intro next env result h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨cv, hc, x, hx, h⟩ := h
    show oEval o env (.un op (freshenUnknowns next value).1) = _
    simp only [oEval, bind_ok]
    exact ⟨cv, ih _ hc, x, hx, h⟩
  | cast kind width value ih =>
    intro next env result h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨cv, hc, x, hx, h⟩ := h
    show oEval o env (.cast kind width (freshenUnknowns next value).1) = _
    simp only [oEval, bind_ok]
    exact ⟨cv, ih _ hc, x, hx, h⟩
  | letIn var value body ihv ihb =>
    intro next env result h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨cv, hc, h⟩ := h
    show oEval o env (.letIn var (freshenUnknowns next value).1 (freshenUnknowns _ body).1) = _
    simp only [oEval, bind_ok]
    exact ⟨cv, ihv _ hc, ihb _ h⟩
  | ite condition yes no ihc ihy ihn =>
    intro next env result h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨cv, hc, ⟨w, x⟩, hx, h⟩ := h
    show oEval o env (.ite (freshenUnknowns next condition).1 (freshenUnknowns _ yes).1 (freshenUnknowns _ no).1) = _
    simp only [oEval, bind_ok]
    refine ⟨cv, ihc _ hc, ⟨w, x⟩, hx, ?_⟩
    simp only at h ⊢
    by_cases hw : w = 1
    · subst hw
      simp only [↓reduceDIte] at h ⊢
      split at h
      · rw [ite_eq_left (by assumption)]; exact ihy _ h
      · rw [ite_eq_right (by assumption)]; exact ihn _ h
    · simp [hw] at h
  | extract high low value ih =>
    intro next env result h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨cv, hc, x, hx, y, hy, h⟩ := h
    show oEval o env (.extract high low (freshenUnknowns next value).1) = _
    simp only [oEval, bind_ok]
    exact ⟨cv, ih _ hc, x, hx, y, hy, h⟩
  | concat left right ihl ihr =>
    intro next env value h
    simp only [Bil.evalExp, bind_ok] at h
    obtain ⟨lv, hl, x, hx, rv, hr, y, hy, h⟩ := h
    show oEval o env (.concat (freshenUnknowns next left).1 (freshenUnknowns _ right).1) = _
    simp only [oEval, bind_ok]
    exact ⟨lv, ihl _ hl, x, hx, rv, ihr _ hr, y, hy, h⟩

/-- Without an `unknown` the oracle has no say. -/
theorem oEval_of_noUnknown (o : Oracle) (env : Bil.Env) (e : Bil.Exp) (h : noUnknown e = true) :
    oEval o env e = Bil.evalExp env e := by
  induction e generalizing env <;> simp_all [oEval, Bil.evalExp, noUnknown]
  rfl

/-- A concrete run is a run under any oracle: it doesn't reach an `unknown`, or it would have failed. -/
theorem oExec_of_exec (o : Oracle) (cf : Nat) :
    (∀ (stmt : Bil.Stmt) (env : Bil.Env) (next : Nat) (final : Bil.State × Bil.Effect),
      Bil.execStmt cf { env := env } stmt = .ok final →
      ∃ n, oExecStmt o cf { env := env, unknowns := next } stmt = .ok ({ env := final.1.env, unknowns := n }, final.2)) ∧
    (∀ (program : Bil.Program) (env : Bil.Env) (next : Nat) (final : Bil.State × Bil.Effect),
      Bil.execProgram cf { env := env } program = .ok final →
      ∃ n, oExecProgram o cf { env := env, unknowns := next } program = .ok ({ env := final.1.env, unknowns := n }, final.2)) := by
  induction cf with
  | zero =>
    refine ⟨fun _ _ _ _ h => ?_, fun _ _ _ _ h => ?_⟩
    · rw [Bil.execStmt] at h; cases h
    · rw [Bil.execProgram] at h; cases h
  | succ cf ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro stmt env next final h
      cases stmt with
      | move var value =>
        rw [Bil.execStmt] at h
        rw [oExecStmt]
        obtain ⟨cv, hcv, h⟩ := bind_ok.mp h
        cases h
        exact ⟨_, by simp only [oEval_of_evalExp o value next hcv, bind, Except.bind]; rfl⟩
      | jmp target =>
        rw [Bil.execStmt] at h
        rw [oExecStmt]
        simp only [bind_ok, Bil.execExp] at h
        obtain ⟨cv, hcv, x, hx, h⟩ := h
        cases h
        exact ⟨_, by simp only [oEval_of_evalExp o target next hcv, hx, bind, Except.bind]; rfl⟩
      | special message => rw [Bil.execStmt] at h; rw [oExecStmt]; cases h; exact ⟨_, rfl⟩
      | cpuExn number => rw [Bil.execStmt] at h; rw [oExecStmt]; cases h; exact ⟨_, rfl⟩
      | ifElse condition yes no =>
        rw [Bil.execStmt] at h
        rw [oExecStmt]
        simp only [bind_ok, Bil.execExp] at h
        obtain ⟨cv, hcv, ⟨w, x⟩, hx, h⟩ := h
        simp only at h
        by_cases hw : w = 1
        · subst hw
          simp only [↓reduceDIte] at h
          obtain ⟨n, hn⟩ := ihp _ _ (freshenUnknowns next condition).2 _ h
          exact ⟨n, by simp only [oEval_of_evalExp o condition next hcv, hx, bind, Except.bind, ↓reduceDIte]; exact hn⟩
        · simp [hw] at h
      | «while» condition body =>
        rw [Bil.execStmt] at h
        rw [oExecStmt]
        simp only [bind_ok, Bil.execExp] at h
        obtain ⟨cv, hcv, ⟨w, x⟩, hx, h⟩ := h
        simp only at h
        by_cases hw : w = 1
        · subst hw
          simp only [↓reduceDIte] at h
          simp only [oEval_of_evalExp o condition next hcv, hx, bind, Except.bind, ↓reduceDIte]
          by_cases h1 : x = 1
          · rw [ite_eq_left h1] at h
            rw [ite_eq_left h1]
            obtain ⟨⟨after, effect⟩, hbody, h⟩ := bind_ok.mp h
            obtain ⟨n, hn⟩ := ihp _ _ (freshenUnknowns next condition).2 _ hbody
            simp only [hn]
            cases effect
            case normal =>
              obtain ⟨m, hm⟩ := ihs _ after.env n _ h
              exact ⟨m, hm⟩
            all_goals
              cases h
              exact ⟨n, rfl⟩
          · rw [ite_eq_right h1] at h
            rw [ite_eq_right h1]
            cases h
            exact ⟨_, rfl⟩
        · simp [hw] at h
    · intro program env next final h
      cases program with
      | nil => rw [Bil.execProgram] at h; rw [oExecProgram]; cases h; exact ⟨_, rfl⟩
      | cons stmt rest =>
        rw [Bil.execProgram] at h
        rw [oExecProgram]
        obtain ⟨⟨after, effect⟩, hstmt, h⟩ := bind_ok.mp h
        obtain ⟨n, hn⟩ := ihs _ _ next _ hstmt
        simp only [hn, bind, Except.bind]
        cases effect
        case normal =>
          obtain ⟨m, hm⟩ := ihp _ after.env n _ h
          exact ⟨m, hm⟩
        all_goals
          cases h
          exact ⟨n, rfl⟩

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

/-- A path accounts for a run under an oracle if its condition holds and it ends the same way in a related state, the
unknowns drawn the same, or if the exploration bound stopped it first. -/
def Accounts (σ : Assignment) (results : List Result) (final : OState × Bil.Effect) : Prop :=
  ∃ r ∈ results, PathHolds σ r.state ∧
    (r.outcome = .exhausted ∨ (Rel σ r.state final.1.env ∧ r.state.unknowns = final.1.unknowns ∧
      OutcomeMatches σ r.outcome final.2))

private theorem accounts_of_subset {σ : Assignment} {as bs : List Result} {final : OState × Bil.Effect}
    (h : ∀ x ∈ as, x ∈ bs) (hc : Accounts σ as final) : Accounts σ bs final :=
  let ⟨r, hr, hp⟩ := hc
  ⟨r, h r hr, hp⟩

private theorem rel_unknowns {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) (n : Nat) :
    Rel σ { s with unknowns := n } env :=
  { envSized := h.envSized, memoriesSized := h.memoriesSized, vars := h.vars, mems := h.mems,
    inputs := h.inputs, pages := h.pages }

private theorem rel_withConstraint {σ : Assignment} {s : State} {env : Bil.Env} (h : Rel σ s env) (c : Expr) :
    Rel σ (withConstraint s c) env :=
  { envSized := h.envSized, memoriesSized := h.memoriesSized, vars := h.vars, mems := h.mems,
    inputs := h.inputs, pages := h.pages }

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

private theorem holds_eqOne {σ : Assignment} {x : Expr} (hw : x.width = 1) (hd : denote σ x = ⟨1, 1⟩) :
    Holds σ (Expr.eqOne x) := by
  rw [eqOne_of_width_one hw, Holds, hd]; rfl

private theorem holds_eqZero {σ : Assignment} {x : Expr} (hw : x.width = 1) (hd : denote σ x = ⟨1, 0⟩) :
    Holds σ (Expr.eqZero x) := by
  simp only [Holds, Expr.eqZero]
  rw [const_zero_of_width hw, isOne_denote_eq, hd, denote_const]
  rfl

private theorem freshen_eq (s : State) (e : Bil.Exp) :
    freshen s e = ({ s with unknowns := (freshenUnknowns s.unknowns e).2 }, (freshenUnknowns s.unknowns e).1) := rfl

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
private theorem accounts_sequence {σ : Assignment} {sf : Nat} {o : Oracle} {cf : Nat} {rest : Bil.Program}
    {results qs : List Result} {next : OState} {effect : Bil.Effect} {final : OState × Bil.Effect}
    (hrest : ∀ s rs final, Rel σ s next.env → s.unknowns = next.unknowns → PathHolds σ s →
      executeProgram sf s rest = .ok rs → oExecProgram o cf next rest = .ok final → Accounts σ rs final)
    (hcover : Accounts σ results (next, effect))
    (hq : executeProgram.continueResults sf rest results = .ok qs)
    (hfinal : (match effect with
      | .normal => oExecProgram o cf next rest
      | other => .ok (next, other)) = Except.ok final) :
    Accounts σ qs final := by
  obtain ⟨r, hr, hp, hend⟩ := hcover
  rcases hend with hx | ⟨hrel, hu, hm⟩
  · exact ⟨r, continueProgram_other hq hr (by rw [hx]; simp), hp, .inl hx⟩
  · cases effect
    case normal =>
      obtain ⟨first, hf, hs⟩ := continueProgram_normal hq hr (outcome_normal_of_matches hm)
      exact accounts_of_subset hs (hrest _ _ _ hrel hu hp hf hfinal)
    all_goals
      cases hfinal
      exact ⟨r, continueProgram_other hq hr (outcome_other_of_matches hm (by simp)), hp, .inr ⟨hrel, hu, hm⟩⟩

/-- Symbolic execution is sound under every way of resolving its unknowns: every run of a statement or program under
an oracle that agrees with an assignment, from a state the assignment relates to the symbolic state and whose path
condition it satisfies, is covered by a symbolic path. Holds for loops too, where the bound may stop the path. -/
theorem execute_sound_oracle (σ : Assignment) {o : Oracle} (ho : Agrees σ o) (cf : Nat) :
    (∀ (sf : Nat) (s : State) (stmt : Bil.Stmt) (cs : OState) (rs : List Result) (final : OState × Bil.Effect),
      Rel σ s cs.env → s.unknowns = cs.unknowns → PathHolds σ s → executeStmt sf s stmt = .ok rs →
      oExecStmt o cf cs stmt = .ok final → Accounts σ rs final) ∧
    (∀ (sf : Nat) (s : State) (program : Bil.Program) (cs : OState) (rs : List Result) (final : OState × Bil.Effect),
      Rel σ s cs.env → s.unknowns = cs.unknowns → PathHolds σ s → executeProgram sf s program = .ok rs →
      oExecProgram o cf cs program = .ok final → Accounts σ rs final) := by
  have hpages := fun message w c h => (ho.memory message w c h).2
  induction cf with
  | zero =>
    refine ⟨fun _ _ _ _ _ _ _ _ _ _ hc => ?_, fun _ _ _ _ _ _ _ _ _ _ hc => ?_⟩
    · rw [oExecStmt] at hc; cases hc
    · rw [oExecProgram] at hc; cases hc
  | succ cf ih =>
    obtain ⟨ihs, ihp⟩ := ih
    constructor
    · intro sf s stmt cs rs final hrel hu hpath hsym hc
      cases sf with
      | zero =>
        rw [executeStmt_zero] at hsym
        cases hsym
        exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inl rfl⟩
      | succ sf =>
        cases stmt with
        | move var value =>
          rw [executeStmt, freshen_eq, hu] at hsym
          rw [oExecStmt] at hc
          obtain ⟨cv, hcv, hc⟩ := bind_ok.mp hc
          cases hc
          generalize hfresh : freshenUnknowns cs.unknowns value = fresh at hsym hcv
          obtain ⟨value', n⟩ := fresh
          have hrel' := rel_unknowns hrel n
          have hsound := evalExp_sound σ ho value'
          have hpg := fun {w} {c : Bap.Memory w} (he : cv = .memory c) => pages_evalExp hpages value' hrel.pages (he ▸ hcv)
          simp only at hsym hcv
          split at hsym
          · next hm =>
            obtain ⟨m, hm', hsym⟩ := bind_ok.mp hsym
            cases hsym
            refine ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨?_, by simp [hfresh], trivial⟩⟩
            exact rel_bindMemory hrel' hm ((sized_eval σ value').2 hrel'.toWellSized hm')
              (fun he => hsound.2 hrel' hm' (he ▸ hcv)) hpg
          · next hm =>
            obtain ⟨x, hx, hsym⟩ := bind_ok.mp hsym
            cases hsym
            refine ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨?_, by simp [hfresh], trivial⟩⟩
            exact rel_bind hrel' (by simpa using hm) ((sized_eval σ value').1 hrel'.toWellSized hx)
              (fun he => hsound.1 hrel' hx (he ▸ hcv)) hpg
        | jmp target =>
          rw [executeStmt, freshen_eq, hu] at hsym
          rw [oExecStmt] at hc
          simp only [bind_ok] at hc
          obtain ⟨cv, hcv, ⟨w, t⟩, hb, hc⟩ := hc
          cases cv <;> simp only [Value.asBits, reduceCtorEq] at hb
          cases hb
          cases hc
          obtain ⟨x, hx, hsym⟩ := bind_ok.mp hsym
          cases hsym
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨rel_unknowns hrel _, rfl,
            (evalExp_sound σ ho _).1 (rel_unknowns hrel _) hx hcv⟩⟩
        | special message =>
          rw [executeStmt] at hsym
          rw [oExecStmt] at hc
          cases hsym
          cases hc
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, hu, rfl⟩⟩
        | cpuExn number =>
          rw [executeStmt] at hsym
          rw [oExecStmt] at hc
          cases hsym
          cases hc
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, hu, rfl⟩⟩
        | ifElse condition yes no =>
          rw [executeStmt, freshen_eq, hu] at hsym
          rw [oExecStmt] at hc
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
            have hrel' := rel_unknowns hrel (freshenUnknowns cs.unknowns condition).2
            let drawn : OState := { env := cs.env, unknowns := (freshenUnknowns cs.unknowns condition).2 }
            have hd := (evalExp_sound σ ho _).1 hrel' hx0 hcv
            cases hk : x.knownCondition with
            | some b =>
              rw [hk] at hsym
              have hkb := known_sound hk hd
              cases b
              · have ht : ¬ t = 1 := by simpa using hkb
                rw [ite_eq_right ht] at hc
                exact ihp _ _ _ drawn _ _ hrel' rfl hpath hsym hc
              · have ht : t = 1 := by simpa using hkb
                rw [ite_eq_left ht] at hc
                exact ihp _ _ _ drawn _ _ hrel' rfl hpath hsym hc
            | none =>
              rw [hk] at hsym
              simp only [bind_ok] at hsym
              obtain ⟨ys, hy, ns, hn, hsym⟩ := hsym
              cases hsym
              rcases bit_cases t with rfl | rfl
              · rw [ite_eq_left rfl] at hc
                exact accounts_of_subset (fun _ h => List.mem_append_left _ h)
                  (ihp _ _ _ drawn _ _ (rel_withConstraint hrel' _) rfl
                    (pathHolds_withConstraint hpath (holds_eqOne hxw hd)) hy hc)
              · rw [ite_eq_right (by decide)] at hc
                exact accounts_of_subset (fun _ h => List.mem_append_right _ h)
                  (ihp _ _ _ drawn _ _ (rel_withConstraint hrel' _) rfl
                    (pathHolds_withConstraint hpath (holds_eqZero hxw hd)) hn hc)
          · simp [hw] at hc
        | «while» condition body =>
          rw [executeStmt, freshen_eq, hu] at hsym
          rw [oExecStmt] at hc
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
            have hrel' := rel_unknowns hrel (freshenUnknowns cs.unknowns condition).2
            let drawn : OState := { env := cs.env, unknowns := (freshenUnknowns cs.unknowns condition).2 }
            have hd := (evalExp_sound σ ho _).1 hrel' hx0 hcv
            have hloop : ∀ {results qs : List Result} {next : OState × Bil.Effect},
                Accounts σ results next →
                executeStmt.continueResults sf condition body results = .ok qs →
                (match next.2 with
                  | .normal => oExecStmt o cf next.1 (.while condition body)
                  | other => .ok (next.1, other)) = Except.ok final →
                Accounts σ qs final := by
              intro results qs next hcover hq hfinal
              obtain ⟨r, hr, hp, hend⟩ := hcover
              rcases hend with hxh | ⟨hrelr, hur, hm⟩
              · exact ⟨r, continueWhile_other hq hr (by rw [hxh]; simp), hp, .inl hxh⟩
              · obtain ⟨nextState, effect⟩ := next
                simp only at hfinal hrelr hm hur
                cases effect
                case normal =>
                  obtain ⟨first, hf, hsub⟩ := continueWhile_normal hq hr (outcome_normal_of_matches hm)
                  exact accounts_of_subset hsub (ihs _ _ _ _ _ _ hrelr hur hp hf hfinal)
                all_goals
                  cases hfinal
                  exact ⟨r, continueWhile_other hq hr (outcome_other_of_matches hm (by simp)), hp, .inr ⟨hrelr, hur, hm⟩⟩
            cases hk : x.knownCondition with
            | some b =>
              rw [hk] at hsym
              have hkb := known_sound hk hd
              cases b
              · have ht : ¬ t = 1 := by simpa using hkb
                rw [ite_eq_right ht] at hc
                cases hc
                cases hsym
                exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel', rfl, trivial⟩⟩
              · have ht : t = 1 := by simpa using hkb
                rw [ite_eq_left ht] at hc
                obtain ⟨⟨next, effect⟩, hbody, hc⟩ := bind_ok.mp hc
                obtain ⟨bs, hbs, hq⟩ := bind_ok.mp hsym
                exact hloop (next := (next, effect)) (ihp _ _ _ drawn _ _ hrel' rfl hpath hbs hbody) hq hc
            | none =>
              rw [hk] at hsym
              simp only [bind_ok] at hsym
              obtain ⟨bs, hbs, qs, hq, hsym⟩ := hsym
              cases hsym
              rcases bit_cases t with rfl | rfl
              · rw [ite_eq_left rfl] at hc
                obtain ⟨⟨next, effect⟩, hbody, hc⟩ := bind_ok.mp hc
                exact accounts_of_subset (fun _ h => List.mem_append_left _ h)
                  (hloop (next := (next, effect)) (ihp _ _ _ drawn _ _ (rel_withConstraint hrel' _) rfl
                    (pathHolds_withConstraint hpath (holds_eqOne hxw hd)) hbs hbody) hq hc)
              · rw [ite_eq_right (by decide)] at hc
                cases hc
                exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl),
                  pathHolds_withConstraint hpath (holds_eqZero hxw hd), .inr ⟨rel_withConstraint hrel' _, rfl, trivial⟩⟩
          · simp [hw] at hc
    · intro sf s program cs rs final hrel hu hpath hsym hc
      cases program with
      | nil =>
        rw [executeProgram_nil] at hsym
        rw [oExecProgram] at hc
        cases hsym
        cases hc
        exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inr ⟨hrel, hu, trivial⟩⟩
      | cons stmt rest =>
        cases sf with
        | zero =>
          rw [executeProgram_zero_cons] at hsym
          cases hsym
          exact ⟨_, List.mem_singleton.mpr rfl, hpath, .inl rfl⟩
        | succ sf =>
          rw [executeProgram] at hsym
          rw [oExecProgram] at hc
          obtain ⟨results, hres, hq⟩ := bind_ok.mp hsym
          obtain ⟨⟨next, effect⟩, hstmt, hc⟩ := bind_ok.mp hc
          exact accounts_sequence (next := next) (effect := effect)
            (fun s' rs' final' hr hun hp hsy hcn => ihp _ _ _ _ _ _ hr hun hp hsy hcn)
            (ihs _ _ _ _ _ _ hrel hu hpath hres hstmt) hq hc

/-- Symbolic execution is sound against the BIL evaluator: every concrete run of a statement or program, from a state
an assignment relates to the symbolic state and whose path condition it satisfies, is covered by a symbolic path. A
run the evaluator finishes reaches no `unknown`, whichever others the program has. -/
theorem execute_sound (σ : Assignment) (cf : Nat) :
    (∀ (sf : Nat) (s : State) (stmt : Bil.Stmt) (env : Bil.Env) (rs : List Result) (final : Bil.State × Bil.Effect),
      Rel σ s env → PathHolds σ s → executeStmt sf s stmt = .ok rs →
      Bil.execStmt cf { env := env } stmt = .ok final → Covers σ rs final) ∧
    (∀ (sf : Nat) (s : State) (program : Bil.Program) (env : Bil.Env) (rs : List Result) (final : Bil.State × Bil.Effect),
      Rel σ s env → PathHolds σ s → executeProgram sf s program = .ok rs →
      Bil.execProgram cf { env := env } program = .ok final → Covers σ rs final) := by
  have ho := agrees_ofAssignment σ
  have hcovers : ∀ {rs : List Result} {final : Bil.State × Bil.Effect} {n : Nat},
      Accounts σ rs ({ env := final.1.env, unknowns := n }, final.2) → Covers σ rs final := by
    rintro rs final n ⟨r, hr, hp, hend⟩
    exact ⟨r, hr, hp, hend.imp id fun h => ⟨h.1, h.2.2⟩⟩
  refine ⟨fun sf s stmt env rs final hrel hpath hsym hc => ?_, fun sf s program env rs final hrel hpath hsym hc => ?_⟩
  · obtain ⟨n, hn⟩ := (oExec_of_exec (Oracle.ofAssignment σ) cf).1 stmt env s.unknowns final hc
    exact hcovers ((execute_sound_oracle σ ho cf).1 sf s stmt { env := env, unknowns := s.unknowns } rs _ hrel rfl
      hpath hsym hn)
  · obtain ⟨n, hn⟩ := (oExec_of_exec (Oracle.ofAssignment σ) cf).2 program env s.unknowns final hc
    exact hcovers ((execute_sound_oracle σ ho cf).2 sf s program { env := env, unknowns := s.unknowns } rs _ hrel rfl
      hpath hsym hn)

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
    {final : Bil.State × Bil.Effect} {sf cf : Nat} (hfree : programLoopFree program)
    (hdepth : programDepth program ≤ sf) (hrel : Rel σ s env) (hpath : PathHolds σ s)
    (hsym : run program s sf = .ok rs) (hc : Bil.run program { env := env } cf = .ok final) :
    ∃ r ∈ rs, PathHolds σ r.state ∧ Rel σ r.state final.1.env ∧ OutcomeMatches σ r.outcome final.2 := by
  obtain ⟨r, hr, hp, hend⟩ := (execute_sound σ cf).2 sf s program env rs final hrel hpath hsym hc
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
    simp only [evalExp, bind, Except.bind]
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
    (memoryOf s var).name = inputName var ∧ (memoryOf s var).cells = [] := by
  simp [memoryOf, h]

/-! ### Invariants of execution -/

/-- A property of states preserved by every primitive state change the executor makes. -/
structure StepInvariant (Inv : State → Prop) : Prop where
  constraint : ∀ s e (x : Expr), evalExp s e = .ok x → x.width = 1 → Inv s →
    Inv (withConstraint s x.eqOne) ∧ Inv (withConstraint s x.eqZero)
  unknowns : ∀ s n, Inv s → Inv { s with unknowns := n }
  move : ∀ s var value x, Inv s → evalExp s value = .ok x → Inv { s with env := (var, x) :: s.env }
  memory : ∀ s var value m, Inv s → evalMemory s value = .ok m → Inv { s with memories := (var, m) :: s.memories }

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
        obtain ⟨x0, hx0, x, hx, h⟩ := h
        obtain ⟨rfl, hw⟩ := expectCondition_ok hx
        split at h
        · exact ihp _ _ _ hs' h
        · exact ihp _ _ _ hs' h
        · simp only [bind_ok] at h
          obtain ⟨ys, hy, ns, hn, he⟩ := h
          cases he
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact ihp _ _ _ (hinv.constraint _ _ _ hx0 hw hs').1 hy r hr
          · exact ihp _ _ _ (hinv.constraint _ _ _ hx0 hw hs').2 hn r hr
      | «while» condition body =>
        rw [executeStmt, freshen_eq] at h
        have hs' := hinv.unknowns s (freshenUnknowns s.unknowns condition).2 hs
        simp only [bind_ok] at h
        obtain ⟨x0, hx0, x, hx, h⟩ := h
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
          · exact hcont (ihp _ _ _ (hinv.constraint _ _ _ hx0 hw hs').1 hb) hq r hr
          · exact single (hinv.constraint _ _ _ hx0 hw hs').2 hr
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
  constraint := fun _ _ _ _ _ h => ⟨h.trans (List.prefix_append _ _), h.trans (List.prefix_append _ _)⟩
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
  · intro s _ x _ hw hs
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
  · exact fun _ _ _ _ _ h => ⟨⟨h.envSized, h.memoriesSized⟩, ⟨h.envSized, h.memoriesSized⟩⟩
  · exact fun _ _ h => ⟨h.envSized, h.memoriesSized⟩
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
    {size : Nat} (hcells : MemorySized σ memory) (ha : (denote σ address).1 = address.width)
    (hsize : size ≤ 2 ^ address.width) :
    (denote σ (readValue (memory.write address value endian size) address endian size)).2.toNat =
      (denote σ value).2.toNat % 2 ^ (8 * size) := by
  rw [(denote_read σ _ address endian size (memorySized_write hcells ha _ _ _) ha).2]
  simp only [modelRead]
  have hbytes : ((List.range size).map fun offset =>
      memoryByte σ (memory.write address value endian size) (offsetBits (denote σ address) offset)) =
      (List.range size).map fun offset =>
        valueByte (denote σ value) (match endian with | .little => offset | .big => size - 1 - offset) := by
    apply List.map_congr_left
    intro offset hoff
    rw [memoryByte_write σ memory address value endian size ha,
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

/-! ### More fuel changes nothing once no path is exhausted -/

/-- No path of a result list was stopped by the bound. -/
def Finished (results : List Result) : Prop := ∀ r ∈ results, r.outcome ≠ .exhausted

private theorem finished_append {a b : List Result} (h : Finished (a ++ b)) : Finished a ∧ Finished b :=
  ⟨fun r hr => h r (List.mem_append_left _ hr), fun r hr => h r (List.mem_append_right _ hr)⟩

private theorem continueProgram_stable {f : Nat} {rest : Bil.Program}
    (ih : ∀ s rs, executeProgram f s rest = .ok rs → Finished rs → executeProgram (f + 1) s rest = .ok rs) :
    ∀ (results qs : List Result), executeProgram.continueResults f rest results = .ok qs → Finished qs →
      executeProgram.continueResults (f + 1) rest results = .ok qs := by
  intro results
  induction results with
  | nil =>
    intro qs h _
    rw [executeProgram.continueResults] at h ⊢
    exact h
  | cons r others ihr =>
    intro qs h hf
    rw [continueProgram_cons] at h ⊢
    obtain ⟨first, hfirst, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    obtain ⟨hf1, hf2⟩ := finished_append hf
    simp only [bind_ok]
    refine ⟨first, ?_, others', ihr _ ho hf2, rfl⟩
    cases hn : r.outcome
    case normal =>
      rw [hn] at hfirst
      exact ih _ _ hfirst hf1
    all_goals
      rw [hn] at hfirst
      exact hfirst

private theorem continueWhile_stable {f : Nat} {c : Bil.Exp} {body : Bil.Program}
    (ih : ∀ s rs, executeStmt f s (.while c body) = .ok rs → Finished rs →
      executeStmt (f + 1) s (.while c body) = .ok rs) :
    ∀ (results qs : List Result), executeStmt.continueResults f c body results = .ok qs → Finished qs →
      executeStmt.continueResults (f + 1) c body results = .ok qs := by
  intro results
  induction results with
  | nil =>
    intro qs h _
    rw [executeStmt.continueResults] at h ⊢
    exact h
  | cons r others ihr =>
    intro qs h hf
    rw [continueWhile_cons] at h ⊢
    obtain ⟨first, hfirst, others', ho, h⟩ := by simpa only [bind_ok] using h
    cases h
    obtain ⟨hf1, hf2⟩ := finished_append hf
    simp only [bind_ok]
    refine ⟨first, ?_, others', ihr _ ho hf2, rfl⟩
    cases hn : r.outcome
    case normal =>
      rw [hn] at hfirst
      exact ih _ _ hfirst hf1
    all_goals
      rw [hn] at hfirst
      exact hfirst

/-- A successful run in which no path was stopped by the bound is the same with any more fuel. -/
theorem execute_fuel_stable (f : Nat) :
    (∀ s stmt rs, executeStmt f s stmt = .ok rs → Finished rs → executeStmt (f + 1) s stmt = .ok rs) ∧
      (∀ s program rs, executeProgram f s program = .ok rs → Finished rs →
        executeProgram (f + 1) s program = .ok rs) := by
  induction f with
  | zero =>
    refine ⟨fun s stmt rs h hf => ?_, fun s program rs h hf => ?_⟩
    · rw [executeStmt_zero] at h
      cases h
      exact absurd rfl (hf _ (List.mem_singleton.mpr rfl))
    · cases program with
      | nil => rw [executeProgram_nil] at h ⊢; exact h
      | cons stmt rest =>
        rw [executeProgram_zero_cons] at h
        cases h
        exact absurd rfl (hf _ (List.mem_singleton.mpr rfl))
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    refine ⟨fun s stmt rs h hf => ?_, fun s program rs h hf => ?_⟩
    · cases stmt with
      | move var value => rw [executeStmt] at h ⊢; exact h
      | jmp target => rw [executeStmt] at h ⊢; exact h
      | special message => rw [executeStmt] at h ⊢; exact h
      | cpuExn number => rw [executeStmt] at h ⊢; exact h
      | ifElse condition yes no =>
        rw [executeStmt, freshen_eq] at h ⊢
        simp only [bind_ok] at h ⊢
        obtain ⟨x0, hx0, x, hx, h⟩ := h
        refine ⟨x0, hx0, x, hx, ?_⟩
        cases hk : x.knownCondition with
        | some b =>
          rw [hk] at h
          cases b
          · exact ihp _ _ _ h hf
          · exact ihp _ _ _ h hf
        | none =>
          rw [hk] at h
          simp only [bind_ok] at h ⊢
          obtain ⟨ys, hy, ns, hn, he⟩ := h
          cases he
          obtain ⟨hf1, hf2⟩ := finished_append hf
          exact ⟨ys, ihp _ _ _ hy hf1, ns, ihp _ _ _ hn hf2, rfl⟩
      | «while» condition body =>
        rw [executeStmt, freshen_eq] at h ⊢
        simp only [bind_ok] at h ⊢
        obtain ⟨x0, hx0, x, hx, h⟩ := h
        refine ⟨x0, hx0, x, hx, ?_⟩
        have hbody : ∀ {results : List Result} {qs : List Result},
            executeStmt.continueResults f condition body results = .ok qs → Finished qs →
            (∀ r ∈ results, r.outcome ≠ .exhausted) := by
          intro results qs hq hfq r hr he
          exact hfq r (continueWhile_other hq hr (by rw [he]; simp)) he
        have hnormal : ∀ {results : List Result} {qs : List Result},
            executeStmt.continueResults f condition body results = .ok qs → Finished qs →
            executeStmt.continueResults (f + 1) condition body results = .ok qs :=
          fun hq hfq => continueWhile_stable (ihs · _) _ _ hq hfq
        cases hk : x.knownCondition with
        | some b =>
          rw [hk] at h
          cases b
          · exact h
          · simp only [bind_ok] at h ⊢
            obtain ⟨bs, hb, hq⟩ := h
            exact ⟨bs, ihp _ _ _ hb (hbody hq hf), hnormal hq hf⟩
        | none =>
          rw [hk] at h
          simp only [bind_ok] at h ⊢
          obtain ⟨bs, hb, qs, hq, he⟩ := h
          cases he
          obtain ⟨hf1, _⟩ := finished_append hf
          exact ⟨bs, ihp _ _ _ hb (hbody hq hf1), qs, hnormal hq hf1, rfl⟩
    · cases program with
      | nil => rw [executeProgram_nil] at h ⊢; exact h
      | cons stmt rest =>
        rw [executeProgram] at h ⊢
        obtain ⟨results, hres, hq⟩ := bind_ok.mp h
        have hresf : Finished results := by
          intro r hr he
          exact hf r (continueProgram_other hq hr (by rw [he]; simp)) he
        exact bind_ok.mpr ⟨results, ihs _ _ _ hres hresf, continueProgram_stable (ihp · rest) _ _ hq hf⟩

/-- So a finished exploration is the exploration, for any fuel from there on. -/
theorem run_fuel_stable {program : Bil.Program} {s : State} {f g : Nat} {rs : List Result} (hfg : f ≤ g)
    (h : run program s f = .ok rs) (hf : Finished rs) : run program s g = .ok rs := by
  induction hfg with
  | refl => exact h
  | step _ ih => exact (execute_fuel_stable _).2 _ _ _ ih hf

/-! ### Names

Lists of characters split at a separator that one side doesn't contain, which is all the parsing the names need. -/

private theorem split_first {α : Type} {x y : α} {a a' r r' : List α} (hx : x ∉ a) (hx' : x ∉ a') (hy : y ∉ a) (hy' : y ∉ a')
    (h : a ++ x :: r = a' ++ y :: r') : a = a' ∧ x = y ∧ r = r' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa using h
    | cons c rest =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hx'
  | cons c rest ih =>
    cases a' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hy
    | cons c' rest' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨he, h⟩ := h
      subst he
      obtain ⟨rfl, h2, h3⟩ := ih (fun m => hx (List.mem_cons_of_mem _ m)) (fun m => hx' (List.mem_cons_of_mem _ m))
        (fun m => hy (List.mem_cons_of_mem _ m)) (fun m => hy' (List.mem_cons_of_mem _ m)) h
      exact ⟨rfl, h2, h3⟩

private theorem split_at {α : Type} {x : α} {a a' r r' : List α} (hx : x ∉ a) (hx' : x ∉ a')
    (h : a ++ x :: r = a' ++ x :: r') : a = a' ∧ r = r' :=
  let ⟨h1, _, h3⟩ := split_first hx hx' hx hx' h
  ⟨h1, h3⟩

private theorem split_last {α : Type} {x : α} {a a' r r' : List α} (hx : x ∉ r) (hx' : x ∉ r')
    (h : a ++ x :: r = a' ++ x :: r') : a = a' ∧ r = r' := by
  have hrev := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append] at hrev
  obtain ⟨h1, h2⟩ := split_at (x := x) (a := r.reverse) (a' := r'.reverse) (by simpa using hx) (by simpa using hx') hrev
  exact ⟨List.reverse_inj.mp h2, List.reverse_inj.mp h1⟩

private theorem toList_toString (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]

private theorem digit_of_mem {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

private theorem not_mem_digits {n : Nat} {c : Char} (h : c.isDigit = false) : c ∉ Nat.toDigits 10 n :=
  fun hm => by rw [digit_of_mem hm] at h; cases h

private theorem digits_inj {a b : Nat} (h : Nat.toDigits 10 a = Nat.toDigits 10 b) : a = b := by
  have he : Nat.repr a = Nat.repr b := by
    rw [← Nat.toString_eq_repr, ← Nat.toString_eq_repr]
    exact String.toList_inj.mp (by rw [toList_toString, toList_toString, h])
  have ha := Nat.toNat?_repr a
  rw [he, Nat.toNat?_repr b] at ha
  exact (Option.some.inj ha).symm

private theorem typeName_toList (typ : Typ) : (typeName typ).toList = match typ with
    | .unknown => ['x']
    | .unit => ['u']
    | .mem a v => 'm' :: Nat.toDigits 10 a ++ '_' :: Nat.toDigits 10 v
    | .imm w => 'b' :: Nat.toDigits 10 w := by
  cases typ <;> simp [typeName, String.toList_append, toList_toString] <;> rfl

private theorem hash_not_mem_typeName (typ : Typ) : '#' ∉ (typeName typ).toList := by
  rw [typeName_toList]
  have hd : ∀ {n : Nat}, '#' ∉ Nat.toDigits 10 n := not_mem_digits (by decide)
  cases typ <;> simp [hd]

private theorem typeName_inj {a b : Typ} (h : typeName a = typeName b) : a = b := by
  have hl := congrArg String.toList h
  rw [typeName_toList, typeName_toList] at hl
  have hu : ∀ {n : Nat}, '_' ∉ Nat.toDigits 10 n := not_mem_digits (by decide)
  cases a <;> cases b <;> simp at hl
  all_goals try rfl
  case mem.mem =>
    obtain ⟨h1, h2⟩ := split_at hu hu hl
    rw [digits_inj h1, digits_inj h2]
  case imm.imm => rw [digits_inj hl]

private theorem inputName_toList (var : Bap.Var) : (inputName var).toList =
    (var.name.toList ++ '#' :: (Nat.toDigits 10 var.index ++ '#' :: (typeName var.typ).toList)) ++ '#' ::
      [if var.isVirtual then 'v' else 'r'] := by
  simp only [inputName, String.toList_append, toList_toString]
  cases var.isVirtual <;> simp <;> rfl

/-- Different variables have different inputs: the name, the index, the type and whether it's virtual all count. -/
theorem inputName_injective {a b : Bap.Var} (h : inputName a = inputName b) : a = b := by
  have hl := congrArg String.toList h
  rw [inputName_toList, inputName_toList] at hl
  have hbit : ∀ {v : Bool}, '#' ∉ [if v = true then 'v' else 'r'] := by intro v; cases v <;> decide
  have hd : ∀ {n : Nat}, '#' ∉ Nat.toDigits 10 n := not_mem_digits (by decide)
  obtain ⟨h1, h2⟩ := split_last hbit hbit hl
  obtain ⟨h3, h4⟩ := split_last (hash_not_mem_typeName _) (hash_not_mem_typeName _) (show
    (a.name.toList ++ '#' :: Nat.toDigits 10 a.index) ++ '#' :: _ =
    (b.name.toList ++ '#' :: Nat.toDigits 10 b.index) ++ '#' :: _ by simpa using h1)
  obtain ⟨h5, h6⟩ := split_last hd hd h3
  have hname := String.toList_inj.mp h5
  have hindex := digits_inj h6
  have htyp := typeName_inj (String.toList_inj.mp h4)
  have hv : a.isVirtual = b.isVirtual := by
    revert h2
    cases a.isVirtual <;> cases b.isVirtual <;> simp
  obtain ⟨an, at', ai, av⟩ := a
  obtain ⟨bn, bt, bi, bv⟩ := b
  simp only at hname hindex htyp hv
  subst hname hindex htyp hv
  rfl

private theorem unknownName_toList (message : String) :
    (unknownName message).toList = "unknown_".toList ++ message.toList ++ ['?'] := by
  simp [unknownName, String.toList_append, toString]

/-- No input has the name of an unknown. -/
theorem inputName_ne_unknownName (var : Bap.Var) (message : String) : inputName var ≠ unknownName message := by
  intro h
  have hl := congrArg (fun name => name.toList.getLast?) h
  have hi : ∃ front, (inputName var).toList = front ++ [if var.isVirtual then 'v' else 'r'] :=
    ⟨(var.name.toList ++ '#' :: (Nat.toDigits 10 var.index ++ '#' :: (typeName var.typ).toList)) ++ ['#'], by
      rw [inputName_toList]; simp⟩
  obtain ⟨front, hf⟩ := hi
  simp only [hf, unknownName_toList, List.getLast?_append, List.getLast?_singleton, Option.some_or] at hl
  split at hl <;> simp at hl

/-- What an unknown's name says about its message. -/
def unknownMessage (name : String) : String := String.ofList (name.toList.drop 8).dropLast

theorem unknownMessage_unknownName (message : String) : unknownMessage (unknownName message) = message := by
  simp [unknownMessage, unknownName_toList]

/-! ### Inputs: from the empty state, any concrete environment and oracle have their assignment -/

/-- The assignment that gives each input the value a concrete environment binds it to, and each unknown the value an
oracle gives it. -/
def inputAssignment (env : Bil.Env) (o : Oracle) : Assignment where
  var name width :=
    match env.find? fun binding => inputName binding.1 == name with
    | some ⟨_, @Value.bits w v⟩ => if h : w = width then h ▸ v else 0
    | some _ => 0
    | none => o.bits (unknownMessage name) width
  memory name width address :=
    match env.find? fun binding => inputName binding.1 == name with
    | some ⟨_, @Value.memory w c⟩ =>
      if h : width = w then (Bap.Memory.readByte c (h ▸ address)).toBitVec else 0
    | some _ => 0
    | none =>
      match o.memory (unknownMessage name) width with
      | some c => (Bap.Memory.readByte c address).toBitVec
      | none => 0

/-- What a concrete environment must look like to be an input: each register is as wide as its type says, and its
memories have whole pages. -/
structure InputEnv (env : Bil.Env) : Prop where
  widths : ∀ var w (v : BitVec w), isMemoryType var.typ = false → Bil.lookup env var = .ok (.bits v) →
    typeWidth var.typ = w
  pages : ∀ var w (concrete : Bap.Memory w), Bil.lookup env var = .ok (.memory concrete) → PagesSized concrete

private theorem find?_congr {α : Type} {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih fun x hx => h x (by simp [hx])]

private theorem find_input {env : Bil.Env} {var : Bap.Var} {value : Value} (hl : Bil.lookup env var = .ok value) :
    (env.find? fun binding => inputName binding.1 == inputName var) = some (var, value) := by
  unfold Bil.lookup at hl
  split at hl
  · next b hfind =>
    cases hl
    have hvar : b.1 = var := by simpa using List.find?_some hfind
    have hcongr : (env.find? fun binding => inputName binding.1 == inputName var) =
        env.find? fun binding => binding.1 == var := by
      apply find?_congr
      intro x _
      show (inputName x.1 == inputName var) = (x.1 == var)
      by_cases hxv : x.1 = var
      · simp [hxv]
      · have : inputName x.1 ≠ inputName var := fun he => hxv (inputName_injective he)
        rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr hxv]
    rw [hcongr, hfind]
    obtain ⟨b1, b2⟩ := b
    cases (show b1 = var from hvar)
    rfl
  · cases hl

private theorem find_unknown (env : Bil.Env) (message : String) :
    (env.find? fun binding => inputName binding.1 == unknownName message) = none := by
  rw [List.find?_eq_none]
  intro b _
  simpa using inputName_ne_unknownName b.1 message

/-- The assignment of an environment and an oracle agrees with the oracle. -/
theorem agrees_inputAssignment (env : Bil.Env) {o : Oracle}
    (hpages : ∀ message w (c : Bap.Memory w), o.memory message w = some c → PagesSized c) :
    Agrees (inputAssignment env o) o where
  bits message width := by
    simp only [inputAssignment, find_unknown, unknownMessage_unknownName]
  memory message w c hc := by
    refine ⟨fun address => ?_, hpages _ _ _ hc⟩
    simp [memoryByte, byteMap, baseByte, inputAssignment, find_unknown, unknownMessage_unknownName, hc]

/-- Every concrete input environment is related to the empty symbolic state, by its own assignment: all of
its registers and memories start as unconstrained inputs. -/
theorem rel_initial {env : Bil.Env} (h : InputEnv env) (o : Oracle) : Rel (inputAssignment env o) {} env where
  envSized := fun _ he => by cases he
  memoriesSized := fun _ he => by cases he
  vars := fun _ _ _ _ _ hg _ => by simp [Assoc.get] at hg
  mems := by
    intro var w c _ hl address
    have hm : memoryOf ({} : State) var = { name := inputName var } := by simp [memoryOf, Assoc.get]
    simp only [hm, memoryByte, byteMap, baseByte, inputAssignment, find_input hl]
    simp
  inputs := by
    intro var w v hm _ hl
    have hw := h.widths var w v hm hl
    rw [denote_var, hw]
    simp [inputAssignment, find_input hl]
  pages := h.pages

/-- An oracle that picks no memory, for the runs that reach no `unknown`. -/
def Oracle.none : Oracle where
  bits _ _ := 0
  memory _ _ := Option.none

/-- `bap symbolic` covers every concrete run from every input, whatever unknowns the program has. -/
theorem run_sound_from_inputs {env : Bil.Env} (h : InputEnv env) {program : Bil.Program} {sf cf : Nat}
    {rs : List Result} {final : Bil.State × Bil.Effect}
    (hsym : run program {} sf = .ok rs) (hc : Bil.run program { env := env } cf = .ok final) :
    Covers (inputAssignment env Oracle.none) rs final :=
  (execute_sound _ cf).2 sf {} program env rs final (rel_initial h _) (fun _ hc => by cases hc) hsym hc

/-- The headline for unknowns: `bap symbolic` covers every run from every input under every oracle, in which each
`unknown` it reaches has a value of its own. The state it ends in is related to that of the run. -/
theorem run_sound_with_oracle {env : Bil.Env} (h : InputEnv env) {o : Oracle}
    (hpages : ∀ message w (c : Bap.Memory w), o.memory message w = some c → PagesSized c) {program : Bil.Program}
    {sf cf : Nat} {rs : List Result} {final : OState × Bil.Effect} (hsym : run program {} sf = .ok rs)
    (hc : oExecProgram o cf { env := env } program = .ok final) : Accounts (inputAssignment env o) rs final :=
  (execute_sound_oracle _ (agrees_inputAssignment env hpages) cf).2 sf {} program { env := env } rs final
    (rel_initial h o) rfl (fun _ hc => by cases hc) hsym hc

/-- With the fuel for its depth, a loop-free program has a finished path for each such run. -/
theorem run_sound_loop_free_oracle {env : Bil.Env} (h : InputEnv env) {o : Oracle}
    (hpages : ∀ message w (c : Bap.Memory w), o.memory message w = some c → PagesSized c) {program : Bil.Program}
    {sf cf : Nat} {rs : List Result} {final : OState × Bil.Effect} (hfree : programLoopFree program)
    (hdepth : programDepth program ≤ sf) (hsym : run program {} sf = .ok rs)
    (hc : oExecProgram o cf { env := env } program = .ok final) :
    ∃ r ∈ rs, PathHolds (inputAssignment env o) r.state ∧ Rel (inputAssignment env o) r.state final.1.env ∧
      OutcomeMatches (inputAssignment env o) r.outcome final.2 := by
  obtain ⟨r, hr, hp, hend⟩ := run_sound_with_oracle h hpages hsym hc
  rcases hend with he | ⟨hrel, _, hm⟩
  · exact absurd he ((execute_complete_of_depth sf).2 {} program rs hfree hdepth hsym r hr)
  · exact ⟨r, hr, hp, hrel, hm⟩

/-! ### Well-typed programs don't fail

The type checker rejects whatever the executor does: a store that overlaps itself, and anything with no bits, which
SMT-LIB has no sort for. -/

open Bap.Bil (inferExp checkStmt checkProgram)
open_private_decls Bap.Bil.Typecheck Bap.Bil expectImm expectSameType expectBits checkCondition

private theorem expectBits_ok {t t' : Typ} (h : expectBits t = .ok t') :
    t' = t ∧ (isMemoryType t = true ∨ typeWidth t ≠ 0) := by
  cases t with
  | unknown =>
    simp only [expectBits, Except.ok.injEq] at h
    exact ⟨h.symm, .inr (by decide)⟩
  | unit =>
    simp only [expectBits, Except.ok.injEq] at h
    exact ⟨h.symm, .inr (by decide)⟩
  | imm w =>
    cases w with
    | zero => simp [expectBits] at h
    | succ n =>
      simp only [expectBits, Except.ok.injEq] at h
      exact ⟨h.symm, .inr (by simp [typeWidth])⟩
  | mem a v =>
    cases a with
    | zero => simp [expectBits] at h
    | succ a =>
      cases v with
      | zero => simp [expectBits] at h
      | succ v =>
        simp only [expectBits, Except.ok.injEq] at h
        exact ⟨h.symm, .inl rfl⟩

/-- The cells of a memory, all the way down, are declared as bytes. -/
inductive MemoryBytes : Bap.Symbolic.Memory → Prop where
  | plain (name cells) : (∀ cell ∈ cells, cell.2.width = 8) → MemoryBytes ⟨name, none, cells⟩
  | branch (name condition yes no cells) : MemoryBytes yes → MemoryBytes no → (∀ cell ∈ cells, cell.2.width = 8) →
      MemoryBytes ⟨name, some (condition, yes, no), cells⟩

theorem MemoryBytes.cells {memory : Bap.Symbolic.Memory} (h : MemoryBytes memory) :
    ∀ cell ∈ memory.cells, cell.2.width = 8 := by
  cases h <;> assumption

theorem width_readInitial' {memory : Bap.Symbolic.Memory} (h : MemoryBytes memory) (address : Expr) :
    (Memory.readInitial memory address).width = 8 := by
  induction h with
  | plain name cells _ => rfl
  | branch name condition yes no cells hy _ _ ihy _ => exact width_readCells hy.cells ihy address

theorem memoryBytes_writeByte {memory : Bap.Symbolic.Memory} (h : MemoryBytes memory) (address : Expr) {value : Expr}
    (hv : value.width = 8) : MemoryBytes (memory.writeByte address value) := by
  have hc : ∀ cell ∈ (memory.writeByte address value).cells, cell.2.width = 8 := by
    intro cell hcell
    rcases List.mem_cons.mp hcell with rfl | hcell
    · exact hv
    · exact h.cells cell (List.mem_filter.mp hcell).1
  cases h with
  | plain name cells _ => exact .plain _ _ hc
  | branch name condition yes no cells hy hn _ => exact .branch _ _ _ _ _ hy hn hc

theorem memoryBytes_write {memory : Bap.Symbolic.Memory} (h : MemoryBytes memory) (address value : Expr)
    (endian : Endian) (size : Nat) : MemoryBytes (memory.write address value endian size) := by
  rw [write_eq_prefix]
  have : ∀ k, MemoryBytes (writePrefix memory address value endian size k) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih =>
      rw [writePrefix_succ]
      exact memoryBytes_writeByte ih _ (by simp only [byteAt, Expr.width]; omega)
  exact this size

/-- The state a well-typed program can run from: registers are as wide as their types. -/
structure Typed (s : State) : Prop where
  env : ∀ var x, Assoc.get var s.env = some x → isMemoryType var.typ = false → x.width = typeWidth var.typ
  memories : ∀ entry ∈ s.memories, MemoryBytes entry.2

theorem memoryBytes_memoryOf {s : State} (h : Typed s) (var : Bap.Var) : MemoryBytes (memoryOf s var) := by
  unfold memoryOf
  split
  · next memory heq => exact h.memories _ (get_mem heq)
  · exact .plain _ _ (fun _ hc => by cases hc)

private theorem typed_bind {s : State} (h : Typed s) {var : Bap.Var} {x : Expr}
    (hx : isMemoryType var.typ = false → x.width = typeWidth var.typ) : Typed { s with env := (var, x) :: s.env } :=
  ⟨by
    intro var' y hg hm
    by_cases he : var' = var
    · subst he
      rw [get_cons_same] at hg
      cases hg
      exact hx hm
    · rw [get_cons_ne _ _ he] at hg
      exact h.env _ _ hg hm, h.memories⟩

private theorem typed_bindMemory {s : State} (h : Typed s) (var : Bap.Var) {m : Bap.Symbolic.Memory}
    (hm : MemoryBytes m) : Typed { s with memories := (var, m) :: s.memories } :=
  ⟨h.env, fun entry he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact hm
    · exact h.memories entry he⟩

private theorem lookup_bound {env : Env} {var : Bap.Var} {x : Expr} (hm : isMemoryType var.typ = false)
    (hg : Assoc.get var env = some x) : lookup env var = .ok x := by
  unfold lookup
  cases ht : var.typ <;> simp_all [isMemoryType]

private theorem lookup_input {env : Env} {var : Bap.Var} (hm : isMemoryType var.typ = false)
    (hg : Assoc.get var env = none) (hw : typeWidth var.typ ≠ 0) :
    lookup env var = .ok (.var (inputName var) (typeWidth var.typ)) := by
  unfold lookup
  cases ht : var.typ <;> simp_all [isMemoryType]

private theorem expectImm_ok {t : Typ} {n : Nat} : expectImm t = .ok n ↔ t = .imm n := by
  cases t <;> simp [expectImm]

/-- Whatever the widths, `binary` has the width of its operator. -/
private theorem width_binary (op : Bil.BinOp) {left right : Expr} {w : Nat} (hl : left.width = w) (hr : right.width = w) :
    (binary op left right).width =
      typeWidth (if op matches .eq | .neq | .lt | .le | .gt | .ge | .slt | .sle | .sgt | .sge then .imm 1 else .imm w) := by
  rcases binary_cases op left right with h | ⟨a, av, b, bv, c, cv, rfl, rfl, hf, h⟩
  · rw [h]
    cases op <;> simp [binaryApp, Expr.width, typeWidth, hl]
  · rw [h]
    simp only [Expr.width] at hl hr
    subst hl
    subst hr
    obtain ⟨v', hv', hb⟩ := evalBin_same op av bv
    rw [hv'] at hf
    cases hf
    show (bilBinary op av bv).1 = _
    cases op <;> rfl

/-- Loads have the width the type checker assigns them. -/
theorem width_read' {memory : Bap.Symbolic.Memory} (h : MemoryBytes memory) (address : Expr)
    (endian : Endian) (size : Nat) : (readValue memory address endian size).width = typeWidth (.imm (size * 8)) :=
  width_readValue_of (fun _ => width_readCells h.cells (width_readInitial' h _) _) address endian size

/-- Totality: the symbolic evaluation of a well-typed expression succeeds, at the type's width. -/
theorem eval_total (e : Bil.Exp) : ∀ {s : State} {t : Typ}, Typed s → inferExp e = .ok t →
    (isMemoryType t = false → ∃ x, evalExp s e = .ok x ∧ x.width = typeWidth t) ∧
      (isMemoryType t = true → ∃ m, evalMemory s e = .ok m ∧ MemoryBytes m) := by
  induction e with
  | int value =>
    intro s t _ ht
    simp only [inferExp] at ht
    obtain ⟨rfl, hr⟩ := expectBits_ok ht
    have hr' := hr.resolve_left (by simp [isMemoryType])
    refine ⟨fun _ => ⟨.const value, by simpa [evalExp, typeWidth] using hr', rfl⟩, fun hm => by cases hm⟩
  | var var =>
    intro s t hs ht
    simp only [inferExp] at ht
    obtain ⟨rfl, hr⟩ := expectBits_ok ht
    refine ⟨fun hm => ?_, fun hm => ⟨_, by simp [evalMemory, hm], memoryBytes_memoryOf hs var⟩⟩
    have hw : typeWidth var.typ ≠ 0 := by simpa [hm] using hr
    cases hg : Assoc.get var s.env with
    | some x => exact ⟨x, lookup_bound hm hg, hs.env _ _ hg hm⟩
    | none => exact ⟨_, lookup_input hm hg hw, rfl⟩
  | load memory address endian size ihm iha =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tm, htm, ht⟩ := ht
    cases tm
    case mem aw vw =>
      simp only at ht
      split at ht
      · simp only [bind_ok] at ht
        obtain ⟨ta, hta, actual, hia, ht⟩ := ht
        split at ht
        · split at ht
          · cases ht
          · next hz =>
            simp only [Except.ok.injEq] at ht
            subst ht
            rw [expectImm_ok] at hia
            subst hia
            refine ⟨fun _ => ?_, fun hm => by cases hm⟩
            obtain ⟨m, hm, hmb⟩ := (ihm hs htm).2 rfl
            obtain ⟨a, ha, _⟩ := (iha hs hta).1 rfl
            refine ⟨_, by simp [evalExp, hm, ha, read_eq _ _ _ hz, bind, Except.bind]; rfl, ?_⟩
            exact width_read' hmb a endian size
        · cases ht
      · cases ht
    all_goals cases ht
  | store memory address value endian size ihm iha ihv =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tm, htm, ht⟩ := ht
    cases tm
    case mem aw vw =>
      simp only at ht
      split at ht
      · cases ht
      · simp only [bind_ok] at ht
        obtain ⟨ta, hta, actual, hia, ht⟩ := ht
        split at ht
        · cases ht
        · next hactual =>
          have hactual' := Decidable.not_not.mp hactual
          subst hactual'
          simp only [bind_ok] at ht
          obtain ⟨tv, htv, vbits, hiv, ht⟩ := ht
          split at ht
          · cases ht
          · next hvw =>
            split at ht
            · cases ht
            · next hz =>
              split at ht
              · cases ht
              · next hfit =>
                simp only [Except.ok.injEq] at ht
                subst ht
                rw [expectImm_ok] at hia hiv
                subst hia hiv
                refine ⟨fun hm => (by cases hm), fun _ => ?_⟩
                obtain ⟨m, hm, hmb⟩ := (ihm hs htm).2 rfl
                obtain ⟨a, ha, haw⟩ := (iha hs hta).1 rfl
                obtain ⟨x, hx, hxw⟩ := (ihv hs htv).1 rfl
                have hw1 : x.width = size * 8 := by rw [hxw]; exact Decidable.not_not.mp hvw
                have hw2 : size ≤ 2 ^ a.width := by rw [haw]; exact Nat.not_lt.mp hfit
                refine ⟨_, ?_, memoryBytes_write hmb a x endian size⟩
                simp [evalMemory, hm, ha, hx, hz, hw1, bind, Except.bind, Nat.not_lt.mpr hw2]
    all_goals cases ht
  | bin op left right ihl ihr =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tl, htl, tr, htr, lw, hil, rw', hir, ht⟩ := ht
    rw [expectImm_ok] at hil hir
    subst hil hir
    split at ht
    · cases ht
    · next hne =>
      have hsame : lw = rw' := by simpa using hne
      subst hsame
      obtain ⟨l, hl, hlw⟩ := (ihl hs htl).1 rfl
      obtain ⟨r, hrr', hrw⟩ := (ihr hs htr).1 rfl
      have hwidth := width_binary op (w := lw) hlw hrw
      have heval : evalExp s (.bin op left right) = .ok (binary op l r) := by
        simp [evalExp, hl, hrr', hlw, hrw, bind, Except.bind]
      cases op <;> simp only [Except.ok.injEq] at ht <;> subst ht <;>
        exact ⟨fun _ => ⟨_, heval, hwidth⟩, fun hm => by cases hm⟩
  | un op value ih =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tv, htv, w, hiv, ht⟩ := ht
    rw [expectImm_ok] at hiv
    subst hiv
    simp only [Except.ok.injEq] at ht
    subst ht
    obtain ⟨x, hx, hxw⟩ := (ih hs htv).1 rfl
    have he : evalExp s (.un op value) =
        .ok (.app (match op with | .neg => "bvneg" | .not => "bvnot") x.width [x]) := by
      cases op <;> simp [evalExp, hx, bind, Except.bind]
    exact ⟨fun _ => ⟨_, he, hxw⟩, fun hm => by cases hm⟩
  | cast kind width value ih =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tv, htv, w, hiv, ht⟩ := ht
    rw [expectImm_ok] at hiv
    subst hiv
    split at ht
    · cases ht
    · next hz =>
      obtain ⟨x, hx, hxw⟩ := (ih hs htv).1 rfl
      have hxw' : x.width = w := hxw
      have hresult : ∃ r, evalCast kind width x = .ok r ∧ t = .imm width := by
        unfold evalCast
        rw [ite_eq_right hz]
        cases kind
        case high =>
          simp only at ht
          split at ht
          · next hle =>
            simp only [Except.ok.injEq] at ht
            simp only
            rw [ite_eq_right (by rw [hxw']; exact Nat.not_lt.mpr hle)]
            exact ⟨_, rfl, ht.symm⟩
          · cases ht
        case low =>
          simp only at ht
          split at ht
          · next hle =>
            simp only [Except.ok.injEq] at ht
            simp only
            split <;> exact ⟨_, rfl, ht.symm⟩
          · cases ht
        all_goals
          simp only [Except.ok.injEq] at ht
          simp only
          split <;> exact ⟨_, rfl, ht.symm⟩
      obtain ⟨r, hr, rfl⟩ := hresult
      exact ⟨fun _ => ⟨r, by simp [evalExp, hx, hr, bind, Except.bind], width_evalCast hr⟩, fun hm => by cases hm⟩
  | letIn var value body ihv ihb =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tv, htv, ht⟩ := ht
    split at ht
    · cases ht
    · next hne =>
      have htype : var.typ = tv := by simpa using hne
      cases hm : isMemoryType var.typ with
      | true =>
        obtain ⟨m, hmem, hmb⟩ := (ihv hs htv).2 (htype ▸ hm)
        have hb := ihb (typed_bindMemory hs var hmb) ht
        constructor
        · intro ht'
          obtain ⟨x, hx, hxw⟩ := hb.1 ht'
          exact ⟨x, by simp [evalExp, hm, hmem, hx, bind, Except.bind], hxw⟩
        · intro ht'
          obtain ⟨y, hy, hyb⟩ := hb.2 ht'
          exact ⟨y, by simp [evalMemory, hm, hmem, hy, bind, Except.bind], hyb⟩
      | false =>
        obtain ⟨x, hx, hxw⟩ := (ihv hs htv).1 (htype ▸ hm)
        have hb := ihb (typed_bind hs (fun _ => by rw [hxw, htype])) ht
        constructor
        · intro ht'
          obtain ⟨y, hy, hyw⟩ := hb.1 ht'
          exact ⟨y, by simp [evalExp, hm, hx, hy, bind, Except.bind], hyw⟩
        · intro ht'
          obtain ⟨y, hy, hyb⟩ := hb.2 ht'
          exact ⟨y, by simp [evalMemory, hm, hx, hy, bind, Except.bind], hyb⟩
  | ite condition yes no ihc ihy ihn =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tc, htc, cw, hic, ht⟩ := ht
    rw [expectImm_ok] at hic
    subst hic
    split at ht
    · cases ht
    · next hc1 =>
      have hcw : cw = 1 := by simpa using hc1
      subst hcw
      simp only [bind_ok] at ht
      obtain ⟨ty, hty, tn, htn, _, hsame, ht⟩ := ht
      simp only [Except.ok.injEq] at ht
      subst ht
      have htn' : tn = ty := by
        unfold expectSameType at hsame
        split at hsame
        · next he => exact he.symm
        · cases hsame
      subst htn'
      obtain ⟨c, hc, hcw'⟩ := (ihc hs htc).1 rfl
      have hcw1 : c.width = 1 := hcw'
      constructor
      · intro hm
        obtain ⟨y, hy, hyw⟩ := (ihy hs hty).1 hm
        obtain ⟨n, hn, hnw⟩ := (ihn hs htn).1 hm
        refine ⟨.ite c y n, ?_, hyw⟩
        simp [evalExp, hc, hy, hn, hcw1, hyw, hnw, bind, Except.bind]
      · intro hm
        obtain ⟨y, hy, hyb⟩ := (ihy hs hty).2 hm
        obtain ⟨n, hn, hnb⟩ := (ihn hs htn).2 hm
        cases hk : c.knownCondition with
        | some b =>
          cases b
          · exact ⟨n, by simp [evalMemory, hc, hy, hn, hcw1, hk, bind, Except.bind], hnb⟩
          · exact ⟨y, by simp [evalMemory, hc, hy, hn, hcw1, hk, bind, Except.bind], hyb⟩
        | none =>
          exact ⟨{ name := y.name, branch := some (c, y, n) },
            by simp [evalMemory, hc, hy, hn, hcw1, hk, bind, Except.bind],
            .branch _ _ _ _ _ hyb hnb (fun _ hc => by cases hc)⟩
  | extract high low value ih =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tv, htv, w, hiv, ht⟩ := ht
    rw [expectImm_ok] at hiv
    subst hiv
    split at ht
    · cases ht
    · next hlow =>
      split at ht
      · cases ht
      · next hhigh =>
        simp only [Except.ok.injEq] at ht
        subst ht
        obtain ⟨x, hx, hxw⟩ := (ih hs htv).1 rfl
        have hxw' : x.width = w := hxw
        refine ⟨fun _ => ⟨_, by simp [evalExp, hx, hlow, hxw', hhigh, bind, Except.bind]; rfl, ?_⟩, fun hm => by cases hm⟩
        simp only [Expr.width, typeWidth]
        omega
  | concat left right ihl ihr =>
    intro s t hs ht
    simp only [inferExp, bind_ok] at ht
    obtain ⟨tl, htl, lw, hil, tr, htr, rw', hir, ht⟩ := ht
    rw [expectImm_ok] at hil hir
    subst hil hir
    simp only [Except.ok.injEq] at ht
    subst ht
    obtain ⟨l, hl, hlw⟩ := (ihl hs htl).1 rfl
    obtain ⟨r, hrr', hrw⟩ := (ihr hs htr).1 rfl
    refine ⟨fun _ => ⟨_, by simp [evalExp, hl, hrr', bind, Except.bind]; rfl, ?_⟩, fun hm => by cases hm⟩
    simp only [Expr.width, hlw, hrw, typeWidth]
  | unknown message typ =>
    intro s t hs ht
    simp only [inferExp] at ht
    obtain ⟨rfl, hr⟩ := expectBits_ok ht
    refine ⟨fun hm => ?_, fun hm => ⟨{ name := unknownName message }, by simp [evalMemory],
      .plain _ _ (fun _ hc => by cases hc)⟩⟩
    have hw : typeWidth t ≠ 0 := by simpa [hm] using hr
    exact ⟨.var (unknownName message) (typeWidth t), by simp [evalExp, hw], rfl⟩

private theorem infer_freshen (e : Bil.Exp) (next : Nat) : inferExp (freshenUnknowns next e).1 = inferExp e := by
  induction e generalizing next with
  | int value => rfl
  | var var => rfl
  | unknown message typ => rfl
  | load memory address endian size ihm iha =>
    show inferExp (.load (freshenUnknowns next memory).1 (freshenUnknowns _ address).1 endian size) = _
    simp only [inferExp, ihm, iha]
  | store memory address value endian size ihm iha ihv =>
    show inferExp (.store (freshenUnknowns next memory).1 (freshenUnknowns _ address).1
      (freshenUnknowns _ value).1 endian size) = _
    simp only [inferExp, ihm, iha, ihv]
  | bin op left right ihl ihr =>
    show inferExp (.bin op (freshenUnknowns next left).1 (freshenUnknowns _ right).1) = _
    simp only [inferExp, ihl, ihr]
  | un op value ih =>
    show inferExp (.un op (freshenUnknowns next value).1) = _
    simp only [inferExp, ih]
  | cast kind width value ih =>
    show inferExp (.cast kind width (freshenUnknowns next value).1) = _
    simp only [inferExp, ih]
  | letIn var value body ihv ihb =>
    show inferExp (.letIn var (freshenUnknowns next value).1 (freshenUnknowns _ body).1) = _
    simp only [inferExp, ihv, ihb]
  | ite condition yes no ihc ihy ihn =>
    show inferExp (.ite (freshenUnknowns next condition).1 (freshenUnknowns _ yes).1 (freshenUnknowns _ no).1) = _
    simp only [inferExp, ihc, ihy, ihn]
  | extract high low value ih =>
    show inferExp (.extract high low (freshenUnknowns next value).1) = _
    simp only [inferExp, ih]
  | concat left right ihl ihr =>
    show inferExp (.concat (freshenUnknowns next left).1 (freshenUnknowns _ right).1) = _
    simp only [inferExp, ihl, ihr]

private theorem typed_withConstraint {s : State} (h : Typed s) (c : Expr) : Typed (withConstraint s c) :=
  ⟨h.env, h.memories⟩

private theorem typed_unknowns {s : State} (h : Typed s) (n : Nat) : Typed { s with unknowns := n } :=
  ⟨h.env, h.memories⟩

private theorem condition_ok {condition : Bil.Exp} {s : State} (next : Nat) (hs : Typed s)
    (hc : checkCondition condition = .ok ()) :
    ∃ x, evalExp s (freshenUnknowns next condition).1 = .ok x ∧ expectCondition x = .ok x := by
  unfold checkCondition at hc
  simp only [bind_ok] at hc
  obtain ⟨t, ht, w, hi, hc⟩ := hc
  rw [expectImm_ok] at hi
  subst hi
  have hw : w = 1 := by
    split at hc
    · assumption
    · cases hc
  subst hw
  obtain ⟨x, hx, hxw⟩ := (eval_total (freshenUnknowns next condition).1 (s := s) hs (by rw [infer_freshen]; exact ht)).1 rfl
  refine ⟨x, hx, ?_⟩
  simp [expectCondition, show x.width = 1 from hxw]

/-- Totality of execution: at any fuel, a well-typed program from a typed state never fails. -/
theorem execute_total (f : Nat) :
    (∀ s stmt, Typed s → checkStmt stmt = .ok () →
      ∃ rs, executeStmt f s stmt = .ok rs ∧ ∀ r ∈ rs, Typed r.state) ∧
    (∀ s program, Typed s → checkProgram program = .ok () →
      ∃ rs, executeProgram f s program = .ok rs ∧ ∀ r ∈ rs, Typed r.state) := by
  have single : ∀ {t : State} {o : Outcome}, Typed t → ∀ r ∈ [(⟨t, o⟩ : Result)], Typed r.state := by
    intro t o ht r hr
    rw [List.mem_singleton.mp hr]
    exact ht
  induction f with
  | zero =>
    refine ⟨fun s stmt hs _ => ⟨_, executeStmt_zero s stmt, single hs⟩, fun s program hs _ => ?_⟩
    cases program with
    | nil => exact ⟨_, executeProgram_nil 0 s, single hs⟩
    | cons stmt rest => exact ⟨_, executeProgram_zero_cons s stmt rest, single hs⟩
  | succ f ih =>
    obtain ⟨ihs, ihp⟩ := ih
    refine ⟨fun s stmt hs hc => ?_, fun s program hs hc => ?_⟩
    · cases stmt with
      | move var value =>
        rw [checkStmt] at hc
        simp only [bind_ok] at hc
        obtain ⟨t, ht, hc⟩ := hc
        have htype : var.typ = t := by
          split at hc
          · assumption
          · cases hc
        have hs' := typed_unknowns hs (freshenUnknowns s.unknowns value).2
        have ht' : inferExp (freshenUnknowns s.unknowns value).1 = .ok t := by rw [infer_freshen]; exact ht
        rw [executeStmt, freshen_eq]
        simp only
        cases hm : isMemoryType var.typ with
        | true =>
          obtain ⟨m, hm', hb⟩ := (eval_total _ hs' ht').2 (htype ▸ hm)
          exact ⟨[⟨{ { s with unknowns := (freshenUnknowns s.unknowns value).2 } with
              memories := (var, m) :: s.memories }, .normal⟩], by simp [hm', bind, Except.bind],
            single (typed_bindMemory hs' var hb)⟩
        | false =>
          obtain ⟨x, hx, hxw⟩ := (eval_total _ hs' ht').1 (htype ▸ hm)
          exact ⟨[⟨{ { s with unknowns := (freshenUnknowns s.unknowns value).2 } with
              env := (var, x) :: s.env }, .normal⟩], by simp [hx, bind, Except.bind],
            single (typed_bind hs' (fun _ => by rw [hxw, htype]))⟩
      | jmp target =>
        rw [checkStmt] at hc
        simp only [bind_ok] at hc
        obtain ⟨t, ht, w, hi, _⟩ := hc
        rw [expectImm_ok] at hi
        subst hi
        have hs' := typed_unknowns hs (freshenUnknowns s.unknowns target).2
        obtain ⟨x, hx, _⟩ := (eval_total (freshenUnknowns s.unknowns target).1 hs' (by rw [infer_freshen]; exact ht)).1 rfl
        rw [executeStmt, freshen_eq]
        exact ⟨[⟨{ s with unknowns := (freshenUnknowns s.unknowns target).2 }, .jump x⟩],
          by simp [hx, bind, Except.bind], single hs'⟩
      | special message =>
        rw [executeStmt]
        exact ⟨_, rfl, single hs⟩
      | cpuExn number =>
        rw [executeStmt]
        exact ⟨_, rfl, single hs⟩
      | ifElse condition yes no =>
        rw [checkStmt] at hc
        simp only [bind_ok] at hc
        obtain ⟨_, hcc, _, hcy, hcn⟩ := hc
        have hs' := typed_unknowns hs (freshenUnknowns s.unknowns condition).2
        obtain ⟨x, hx, he⟩ := condition_ok s.unknowns hs' hcc
        rw [executeStmt, freshen_eq]
        simp only [hx, he, bind, Except.bind]
        cases hk : x.knownCondition with
        | some b =>
          cases b
          · simpa using ihp _ no hs' hcn
          · simpa using ihp _ yes hs' hcy
        | none =>
          obtain ⟨ys, hy, hyt⟩ := ihp _ yes (typed_withConstraint hs' x.eqOne) hcy
          obtain ⟨ns, hn, hnt⟩ := ihp _ no (typed_withConstraint hs' x.eqZero) hcn
          refine ⟨ys ++ ns, by simp [hy, hn], ?_⟩
          intro r hr
          rcases List.mem_append.mp hr with h | h
          · exact hyt r h
          · exact hnt r h
      | «while» condition body =>
        have hcwhile := hc
        rw [checkStmt] at hc
        simp only [bind_ok] at hc
        obtain ⟨_, hcc, hcb⟩ := hc
        have hs' := typed_unknowns hs (freshenUnknowns s.unknowns condition).2
        obtain ⟨x, hx, he⟩ := condition_ok s.unknowns hs' hcc
        have hcont : ∀ (results : List Result), (∀ r ∈ results, Typed r.state) →
            ∃ qs, executeStmt.continueResults f condition body results = .ok qs ∧ ∀ q ∈ qs, Typed q.state := by
          intro results
          induction results with
          | nil =>
            intro _
            exact ⟨[], by rw [executeStmt.continueResults], fun _ hq => by cases hq⟩
          | cons r others ih =>
            intro hall
            obtain ⟨qs, hq, hqt⟩ := ih fun x hx => hall x (List.mem_cons_of_mem _ hx)
            have hr := hall r (by simp)
            rw [continueWhile_cons]
            cases hn : r.outcome
            case normal =>
              obtain ⟨first, hf, hft⟩ := ihs r.state _ hr hcwhile
              refine ⟨first ++ qs, by simp [hf, hq, bind, Except.bind], ?_⟩
              intro q hq'
              rcases List.mem_append.mp hq' with h | h
              · exact hft q h
              · exact hqt q h
            all_goals
              refine ⟨r :: qs, by simp [hq, bind, Except.bind], ?_⟩
              intro q hq'
              rcases List.mem_cons.mp hq' with rfl | h
              · exact hr
              · exact hqt q h
        rw [executeStmt, freshen_eq]
        simp only [hx, he, bind, Except.bind]
        cases hk : x.knownCondition with
        | some b =>
          cases b
          · exact ⟨_, rfl, single hs'⟩
          · obtain ⟨bs, hb, hbt⟩ := ihp _ body hs' hcb
            obtain ⟨qs, hq, hqt⟩ := hcont bs hbt
            exact ⟨qs, by simp [hb, hq], hqt⟩
        | none =>
          obtain ⟨bs, hb, hbt⟩ := ihp _ body (typed_withConstraint hs' x.eqOne) hcb
          obtain ⟨qs, hq, hqt⟩ := hcont bs hbt
          refine ⟨qs ++ [⟨withConstraint { s with unknowns := (freshenUnknowns s.unknowns condition).2 } x.eqZero,
            .normal⟩], by simp [hb, hq], ?_⟩
          intro r hr
          rcases List.mem_append.mp hr with h | h
          · exact hqt r h
          · exact single (typed_withConstraint hs' x.eqZero) r h
    · cases program with
      | nil => exact ⟨_, executeProgram_nil _ s, single hs⟩
      | cons stmt rest =>
        rw [checkProgram] at hc
        simp only [bind_ok] at hc
        obtain ⟨_, hcs, hcr⟩ := hc
        obtain ⟨results, hres, hall⟩ := ihs s stmt hs hcs
        have hcont : ∀ (results : List Result), (∀ r ∈ results, Typed r.state) →
            ∃ qs, executeProgram.continueResults f rest results = .ok qs ∧ ∀ q ∈ qs, Typed q.state := by
          intro results
          induction results with
          | nil =>
            intro _
            exact ⟨[], by rw [executeProgram.continueResults], fun _ hq => by cases hq⟩
          | cons r others ih =>
            intro hall
            obtain ⟨qs, hq, hqt⟩ := ih fun x hx => hall x (List.mem_cons_of_mem _ hx)
            have hr := hall r (by simp)
            rw [continueProgram_cons]
            cases hn : r.outcome
            case normal =>
              obtain ⟨first, hf, hft⟩ := ihp r.state rest hr hcr
              refine ⟨first ++ qs, by simp [hf, hq, bind, Except.bind], ?_⟩
              intro q hq'
              rcases List.mem_append.mp hq' with h | h
              · exact hft q h
              · exact hqt q h
            all_goals
              refine ⟨r :: qs, by simp [hq, bind, Except.bind], ?_⟩
              intro q hq'
              rcases List.mem_cons.mp hq' with rfl | h
              · exact hr
              · exact hqt q h
        obtain ⟨qs, hq, hqt⟩ := hcont results hall
        rw [executeProgram]
        exact ⟨qs, by simp [hres, hq, bind, Except.bind], hqt⟩

/-- `bap symbolic` never fails on a well-typed program: unset registers are inputs, and running out of fuel is a
result. -/
theorem run_total {program : Bil.Program} (hc : checkProgram program = .ok ()) (f : Nat) :
    ∃ rs, run program {} f = .ok rs :=
  let ⟨rs, h, _⟩ := (execute_total f).2 {} program ⟨fun _ _ hg => by simp [Assoc.get] at hg, fun _ he => by cases he⟩ hc
  ⟨rs, h⟩

/-- So the premise of soundness that the symbolic run succeeded can go: each concrete run of a well-typed program from
each input is covered, with no assumption about the symbolic run at all, nor about what else the program does. -/
theorem run_covers_every_input {env : Bil.Env} (h : InputEnv env) {program : Bil.Program} {cf : Nat}
    {final : Bil.State × Bil.Effect} (hc : checkProgram program = .ok ()) (sf : Nat)
    (hrun : Bil.run program { env := env } cf = .ok final) :
    ∃ rs, run program {} sf = .ok rs ∧ Covers (inputAssignment env Oracle.none) rs final :=
  let ⟨rs, hsym⟩ := run_total hc sf
  ⟨rs, hsym, run_sound_from_inputs h hsym hrun⟩

/-- ...and each run under each oracle. -/
theorem run_accounts_every_input {env : Bil.Env} (h : InputEnv env) {o : Oracle}
    (hpages : ∀ message w (c : Bap.Memory w), o.memory message w = some c → PagesSized c) {program : Bil.Program}
    {cf : Nat} {final : OState × Bil.Effect} (hc : checkProgram program = .ok ()) (sf : Nat)
    (hrun : oExecProgram o cf { env := env } program = .ok final) :
    ∃ rs, run program {} sf = .ok rs ∧ Accounts (inputAssignment env o) rs final :=
  let ⟨rs, hsym⟩ := run_total hc sf
  ⟨rs, hsym, run_sound_with_oracle h hpages hsym hrun⟩

/-! ### Nothing has zero width

SMT-LIB has no bitvector sort of width zero, so `(_ bv0 0)` must never reach a script. The executor rejects each way of
making one. -/

theorem evalExp_load_zero (s : State) (memory address : Bil.Exp) (endian : Endian) {m : Bap.Symbolic.Memory} {a : Expr}
    (hm : evalMemory s memory = .ok m) (ha : evalExp s address = .ok a) :
    evalExp s (.load memory address endian 0) = .error "a load must have at least one byte" := by
  simp [evalExp, hm, ha, read_zero, bind, Except.bind]

theorem evalMemory_store_zero (s : State) (memory address value : Bil.Exp) (endian : Endian) {m : Bap.Symbolic.Memory}
    {a x : Expr} (hm : evalMemory s memory = .ok m) (ha : evalExp s address = .ok a) (hx : evalExp s value = .ok x) :
    evalMemory s (.store memory address value endian 0) = .error "a store must have at least one byte" := by
  simp [evalMemory, hm, ha, hx, bind, Except.bind]

/-! ### Well-sorted SMT-LIB

The sort system of the fragment of SMT-LIB the scripts are in: the Core theory's `=`, `distinct`, `ite`, and the
FixedSizeBitVectors theory, over declared constants and unary functions. The output of `renderScript` is shown to be the
printing of a well-sorted syntax tree, as a string, and so this is about the text Z3 reads. -/

inductive SmtSort where
  | bool
  | bitVec (width : Nat)
  deriving DecidableEq, Repr

/-- The terms of the fragment, by the arity of their head. -/
inductive SmtTerm where
  | symbol (name : String)
  | numeral (value width : Nat)
  | bit (value : Bool)
  | app1 (head : String) (first : SmtTerm)
  | app2 (head : String) (first second : SmtTerm)
  | app3 (head : String) (first second third : SmtTerm)

def SmtTerm.print : SmtTerm → String
  | .symbol name => name
  | .numeral value width => s!"(_ bv{value} {width})"
  | .bit true => "#b1"
  | .bit false => "#b0"
  | .app1 head first => s!"({head} {first.print})"
  | .app2 head first second => s!"({head} {first.print} {second.print})"
  | .app3 head first second third => s!"({head} {first.print} {second.print} {third.print})"

/-- The declared constants and unary functions, with the width of the constant and of the argument. Every function
has `(_ BitVec 8)` as its result. -/
structure SmtSignature where
  constants : List (String × Nat) := []
  functions : List (String × Nat) := []

def SmtSignature.symbols (Γ : SmtSignature) : List String := (Γ.constants ++ Γ.functions).map Prod.fst

def bvArithmetic : List String :=
  ["bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv", "bvurem", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr",
    "bvand", "bvor", "bvxor"]

def bvComparison : List String := ["bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]

/-- The sorts of terms: a term has a sort only if its operator and its arguments' sorts fit. -/
inductive HasSort (Γ : SmtSignature) : SmtTerm → SmtSort → Prop where
  | constant {name width} : (name, width) ∈ Γ.constants → HasSort Γ (.symbol name) (.bitVec width)
  | numeral {value width} : 0 < width → value < 2 ^ width → HasSort Γ (.numeral value width) (.bitVec width)
  | bit (value) : HasSort Γ (.bit value) (.bitVec 1)
  | function {name width address} : (name, width) ∈ Γ.functions → HasSort Γ address (.bitVec width) →
      HasSort Γ (.app1 name address) (.bitVec 8)
  | arithmetic {name width left right} : name ∈ bvArithmetic → HasSort Γ left (.bitVec width) →
      HasSort Γ right (.bitVec width) → HasSort Γ (.app2 name left right) (.bitVec width)
  | comparison {name width left right} : name ∈ bvComparison → HasSort Γ left (.bitVec width) →
      HasSort Γ right (.bitVec width) → HasSort Γ (.app2 name left right) .bool
  | equal {name sort left right} : name = "=" ∨ name = "distinct" → HasSort Γ left sort → HasSort Γ right sort →
      HasSort Γ (.app2 name left right) .bool
  | unary {name width value} : name = "bvneg" ∨ name = "bvnot" → HasSort Γ value (.bitVec width) →
      HasSort Γ (.app1 name value) (.bitVec width)
  | extension {kind extra width value} : kind = "sign_extend" ∨ kind = "zero_extend" →
      HasSort Γ value (.bitVec width) → HasSort Γ (.app1 s!"(_ {kind} {extra})" value) (.bitVec (extra + width))
  | extract {high low width value} : low ≤ high → high < width → HasSort Γ value (.bitVec width) →
      HasSort Γ (.app1 s!"(_ extract {high} {low})" value) (.bitVec (high - low + 1))
  | concat {leftWidth rightWidth left right} : HasSort Γ left (.bitVec leftWidth) → HasSort Γ right (.bitVec rightWidth) →
      HasSort Γ (.app2 "concat" left right) (.bitVec (leftWidth + rightWidth))
  | ite {sort condition yes no} : HasSort Γ condition .bool → HasSort Γ yes sort → HasSort Γ no sort →
      HasSort Γ (.app3 "ite" condition yes no) sort

inductive SmtCommand where
  | setLogic (name : String)
  | declareFun (symbol : String) (width : Nat)
  | declareConst (symbol : String) (width : Nat)
  | assert (term : SmtTerm)
  | checkSat

def SmtCommand.print : SmtCommand → String
  | .setLogic name => s!"(set-logic {name})"
  | .declareFun symbol width => s!"(declare-fun {symbol} ((_ BitVec {width})) (_ BitVec 8))"
  | .declareConst symbol width => s!"(declare-const {symbol} (_ BitVec {width}))"
  | .assert term => s!"(assert {term.print})"
  | .checkSat => "(check-sat)"

/-- A quoted symbol: its bars have nothing in them that ends it or escapes. -/
def ValidSymbol (symbol : String) : Prop :=
  ∃ body, symbol.toList = '|' :: body ++ ['|'] ∧ '|' ∉ body ∧ '\\' ∉ body

/-- A script is well sorted when each symbol is valid, of a sort that exists, declared once and before it's used, and
when each assertion is a formula. -/
inductive ScriptSorted : SmtSignature → List SmtCommand → Prop where
  | nil (Γ) : ScriptSorted Γ []
  | checkSat {Γ rest} : ScriptSorted Γ rest → ScriptSorted Γ (.checkSat :: rest)
  | assert {Γ term rest} : HasSort Γ term .bool → ScriptSorted Γ rest → ScriptSorted Γ (.assert term :: rest)
  | declareFun {Γ symbol width rest} : 0 < width → ValidSymbol symbol → symbol ∉ Γ.symbols →
      ScriptSorted { Γ with functions := (symbol, width) :: Γ.functions } rest →
      ScriptSorted Γ (.declareFun symbol width :: rest)
  | declareConst {Γ symbol width rest} : 0 < width → ValidSymbol symbol → symbol ∉ Γ.symbols →
      ScriptSorted { Γ with constants := (symbol, width) :: Γ.constants } rest →
      ScriptSorted Γ (.declareConst symbol width :: rest)

/-- A script: it names a logic that has its declarations, and is otherwise well sorted. -/
def WellSortedScript : List SmtCommand → Prop
  | .setLogic logic :: rest =>
    ScriptSorted {} rest ∧ (logic = "QF_UFBV" ∨ (logic = "QF_BV" ∧ ∀ symbol width, .declareFun symbol width ∉ rest))
  | _ => False

/-- The expressions whose term is well sorted, at the sort `Expr.width` says. -/
inductive WellSorted : Expr → Prop where
  | var (name) {width : Nat} : 0 < width → WellSorted (.var name width)
  | const {width : Nat} (value : BitVec width) : 0 < width → WellSorted (.const value)
  | arithmetic {name : String} {left right : Expr} : name ∈ bvArithmetic → WellSorted left → WellSorted right →
      left.width = right.width → WellSorted (.app name left.width [left, right])
  | predicate {name : String} {left right : Expr} : Expr.isPredicate name = true → WellSorted left →
      WellSorted right → left.width = right.width → WellSorted (.app name 1 [left, right])
  | unary {name : String} {value : Expr} : name = "bvneg" ∨ name = "bvnot" → WellSorted value →
      WellSorted (.app name value.width [value])
  | extension {kind : String} {width : Nat} {value : Expr} : kind = "sign_extend" ∨ kind = "zero_extend" →
      WellSorted value → value.width < width → WellSorted (.app s!"(_ {kind} {width - value.width})" width [value])
  | extract {high low : Nat} {value : Expr} : WellSorted value → low ≤ high → high < value.width →
      WellSorted (.extract high low value)
  | concat {left right : Expr} : WellSorted left → WellSorted right → WellSorted (.concat left right)
  | ite {condition yes no : Expr} : WellSorted condition → condition.width = 1 → WellSorted yes → WellSorted no →
      yes.width = no.width → WellSorted (.ite condition yes no)
  | select (memory) {address : Expr} : WellSorted address → WellSorted (.select memory address)

/-- Nothing well sorted has zero width. -/
theorem WellSorted.width_pos {e : Expr} (h : WellSorted e) : 0 < e.width := by
  induction h with
  | var _ hw => exact hw
  | const _ hw => exact hw
  | arithmetic _ _ _ _ ihl => exact ihl
  | predicate _ _ _ _ => exact Nat.one_pos
  | unary _ _ ih => exact ih
  | extension _ _ hw => exact Nat.lt_of_le_of_lt (Nat.zero_le _) hw
  | extract _ hl hh => simp only [Expr.width]; omega
  | concat _ _ ihl => simp only [Expr.width]; omega
  | ite _ _ _ _ _ _ ihy => exact ihy
  | select _ _ => show 0 < 8; decide

private theorem str_ext {a b : String} (h : a.toList = b.toList) : a = b := String.toList_inj.mp h

private theorem isPredicate_cases {name : String} (h : Expr.isPredicate name = true) :
    name ∈ bvComparison ∨ name = "=" ∨ name = "distinct" := by
  simp only [Expr.isPredicate, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [bvComparison, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h | h | h | h | h | h <;> simp [h]

private theorem not_predicate_arithmetic {name : String} (h : name ∈ bvArithmetic) : Expr.isPredicate name = false := by
  simp only [bvArithmetic, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

private theorem unary_not_predicate {name : String} (h : name = "bvneg" ∨ name = "bvnot") :
    Expr.isPredicate name = false := by
  rcases h with rfl | rfl <;> decide

private theorem extension_not_predicate (kind : String) (k : Nat) : Expr.isPredicate s!"(_ {kind} {k})" = false := by
  simp only [Expr.isPredicate, List.contains_eq_mem, decide_eq_false_iff_not, List.mem_cons, List.not_mem_nil, or_false]
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h <;> exact extension_ne_literal (by decide) h

private theorem render_unary {name : String} {width : Nat} {value : Expr} (h : Expr.isPredicate name = false) :
    (Expr.app name width [value]).render = s!"({name} {value.render})" := by
  rw [Expr.render]
  simp [h]
  apply str_ext
  simp [String.toList_append, String.toList_intercalate, toString]

private theorem render_binary {name : String} {width : Nat} {left right : Expr} (h : Expr.isPredicate name = false) :
    (Expr.app name width [left, right]).render = s!"({name} {left.render} {right.render})" := by
  rw [Expr.render]
  simp [h]
  apply str_ext
  simp [String.toList_append, String.toList_intercalate, toString]

private theorem render_predicate {name : String} {width : Nat} {left right : Expr} (h : Expr.isPredicate name = true) :
    (Expr.app name width [left, right]).render =
      (SmtTerm.app3 "ite" (.app2 name (.symbol left.render) (.symbol right.render)) (.bit true) (.bit false)).print := by
  rw [Expr.render]
  simp [h, SmtTerm.print]
  apply str_ext
  simp [String.toList_append, String.toList_intercalate, toString]

/-- The term of a condition: the formula that a one-bit term is one. -/
private def conditionTerm (t : SmtTerm) : SmtTerm := .app2 "=" t (.bit true)

private theorem HasSort.weaken {Γ Δ : SmtSignature} (hc : ∀ x ∈ Γ.constants, x ∈ Δ.constants)
    (hf : ∀ x ∈ Γ.functions, x ∈ Δ.functions) {t : SmtTerm} {sort : SmtSort} (h : HasSort Γ t sort) : HasSort Δ t sort := by
  induction h with
  | constant h => exact .constant (hc _ h)
  | numeral h1 h2 => exact .numeral h1 h2
  | bit value => exact .bit value
  | function h _ ih => exact .function (hf _ h) ih
  | arithmetic h _ _ ihl ihr => exact .arithmetic h ihl ihr
  | comparison h _ _ ihl ihr => exact .comparison h ihl ihr
  | equal h _ _ ihl ihr => exact .equal h ihl ihr
  | unary h _ ih => exact .unary h ih
  | extension h _ ih => exact .extension h ih
  | extract h1 h2 _ ih => exact .extract h1 h2 ih
  | concat _ _ ihl ihr => exact .concat ihl ihr
  | ite _ _ _ ihc ihy ihn => exact .ite ihc ihy ihn

/-- A signature declares what an expression reads. -/
def Declares (Γ : SmtSignature) (e : Expr) : Prop :=
  (∀ v ∈ e.vars, (Expr.variableSymbol v.1 v.2, v.2) ∈ Γ.constants) ∧
    (∀ m ∈ e.memories, (Expr.memorySymbol m.1 m.2, m.2) ∈ Γ.functions)

/-- Each well-sorted expression renders as a term of the sort of its width, given its declarations. -/
theorem render_hasSort {Γ : SmtSignature} {e : Expr} (h : WellSorted e) (hd : Declares Γ e) :
    ∃ t : SmtTerm, t.print = e.render ∧ HasSort Γ t (.bitVec e.width) := by
  induction h with
  | @var name width hw =>
    refine ⟨.symbol (Expr.variableSymbol name width), by rw [Expr.render]; rfl, .constant (hd.1 (name, width) ?_)⟩
    simp [Expr.vars]
  | @const width value hw =>
    exact ⟨.numeral value.toNat width, by rw [Expr.render]; rfl, .numeral hw value.isLt⟩
  | arithmetic hname _ _ hw ihl ihr =>
    obtain ⟨l, hl, hls⟩ := ihl ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inl hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inl hv)⟩
    obtain ⟨r, hr, hrs⟩ := ihr ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inr hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inr hv)⟩
    refine ⟨.app2 _ l r, ?_, .arithmetic hname hls (hw ▸ hrs)⟩
    rw [render_binary (not_predicate_arithmetic hname)]
    simp [SmtTerm.print, hl, hr]
  | @predicate name left right hname _ _ hw ihl ihr =>
    obtain ⟨l, hl, hls⟩ := ihl ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inl hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inl hv)⟩
    obtain ⟨r, hr, hrs⟩ := ihr ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inr hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inr hv)⟩
    refine ⟨.app3 "ite" (.app2 name l r) (.bit true) (.bit false), ?_, .ite ?_ (.bit _) (.bit _)⟩
    · rw [render_predicate hname]
      simp [SmtTerm.print, hl, hr]
    · rcases isPredicate_cases hname with hc | he | he
      · exact .comparison hc hls (hw ▸ hrs)
      · exact .equal (.inl he) hls (hw ▸ hrs)
      · exact .equal (.inr he) hls (hw ▸ hrs)
  | unary hname _ ih =>
    obtain ⟨v, hv, hvs⟩ := ih ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact hv)⟩
    refine ⟨.app1 _ v, ?_, .unary hname hvs⟩
    rw [render_unary (unary_not_predicate hname)]
    simp [SmtTerm.print, hv]
  | @extension kind width value hkind _ hw ih =>
    obtain ⟨v, hv, hvs⟩ := ih ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact hv)⟩
    refine ⟨.app1 s!"(_ {kind} {width - value.width})" v, ?_, ?_⟩
    · rw [render_unary (extension_not_predicate kind _)]
      simp [SmtTerm.print, hv]
    · have := HasSort.extension (extra := width - value.width) hkind hvs
      rwa [Nat.sub_add_cancel (Nat.le_of_lt hw)] at this
  | @extract high low value _ hl hh ih =>
    obtain ⟨v, hv, hvs⟩ := ih ⟨fun v hv => hd.1 v (by simpa [Expr.vars] using hv),
      fun v hv => hd.2 v (by simpa [Expr.memories] using hv)⟩
    refine ⟨.app1 s!"(_ extract {high} {low})" v, ?_, ?_⟩
    · rw [Expr.render]
      apply str_ext
      simp [SmtTerm.print, hv, String.toList_append, toString]
    · have := HasSort.extract hl hh hvs
      rwa [show high - low + 1 = high + 1 - low by omega] at this
  | concat _ _ ihl ihr =>
    obtain ⟨l, hl, hls⟩ := ihl ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inl hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inl hv)⟩
    obtain ⟨r, hr, hrs⟩ := ihr ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inr hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inr hv)⟩
    refine ⟨.app2 "concat" l r, ?_, .concat hls hrs⟩
    rw [Expr.render]
    apply str_ext
    simp [SmtTerm.print, hl, hr, String.toList_append, toString]
  | @ite condition yes no _ hcw _ _ hw ihc ihy ihn =>
    obtain ⟨c, hc, hcs⟩ := ihc ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inl hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inl hv)⟩
    obtain ⟨y, hy, hys⟩ := ihy ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inr (.inl hv)),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inr (.inl hv))⟩
    obtain ⟨n, hn, hns⟩ := ihn ⟨fun v hv => hd.1 v (by simp [Expr.vars]; exact .inr (.inr hv)),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inr (.inr hv))⟩
    refine ⟨.app3 "ite" (conditionTerm c) y n, ?_, .ite (.equal (.inl rfl) (hcw ▸ hcs) (.bit _)) hys (hw ▸ hns)⟩
    rw [Expr.render]
    apply str_ext
    simp [SmtTerm.print, conditionTerm, hc, hy, hn, String.toList_append, toString]
  | @select memory address _ ih =>
    obtain ⟨a, ha, has⟩ := ih ⟨fun v hv => hd.1 v (by simpa [Expr.vars] using hv),
      fun v hv => hd.2 v (by simp [Expr.memories]; exact .inr hv)⟩
    refine ⟨.app1 _ a, ?_, .function (hd.2 (memory, address.width) (by simp [Expr.memories])) has⟩
    rw [Expr.render]
    simp [SmtTerm.print, ha]

/-- The assertion of a well-sorted expression is a formula. -/
theorem renderFormula_hasSort {Γ : SmtSignature} {e : Expr} (h : WellSorted e) (hd : Declares Γ e) :
    ∃ t : SmtTerm, t.print = e.renderFormula ∧ HasSort Γ t .bool := by
  have hplain : ∀ t : SmtTerm, t.print = e.render → HasSort Γ t (.bitVec e.width) →
      ∃ f : SmtTerm, f.print = s!"(= {e.render} {if e.width = 1 then "#b1" else s!"(_ bv1 {e.width})"})" ∧
        HasSort Γ f .bool := by
    intro t hp hs
    have hw := h.width_pos
    by_cases h1 : e.width = 1
    · refine ⟨.app2 "=" t (.bit true), ?_, .equal (.inl rfl) (h1 ▸ hs) (.bit _)⟩
      rw [ite_eq_left h1]
      simp only [SmtTerm.print, hp]
      rfl
    · refine ⟨.app2 "=" t (.numeral 1 e.width), ?_,
        .equal (.inl rfl) hs (.numeral hw (Nat.one_lt_two_pow (by omega)))⟩
      rw [ite_eq_right h1]
      simp only [SmtTerm.print, hp]
      rfl
  obtain ⟨t, hp, hs⟩ := render_hasSort h hd
  obtain ⟨f, hf, hfs⟩ := hplain t hp hs
  cases h with
  | @predicate name left right hname hl hr hw =>
    have hd' := hd
    obtain ⟨l, hlp, hls⟩ := render_hasSort hl ⟨fun v hv => hd'.1 v (by simp [Expr.vars]; exact .inl hv),
      fun v hv => hd'.2 v (by simp [Expr.memories]; exact .inl hv)⟩
    obtain ⟨r, hrp, hrs⟩ := render_hasSort hr ⟨fun v hv => hd'.1 v (by simp [Expr.vars]; exact .inr hv),
      fun v hv => hd'.2 v (by simp [Expr.memories]; exact .inr hv)⟩
    refine ⟨.app2 name l r, ?_, ?_⟩
    · simp only [Expr.renderFormula, hname, List.isEmpty_cons, Bool.not_false, Bool.and_self, ↓reduceIte]
      apply str_ext
      simp [SmtTerm.print, hlp, hrp, String.toList_append, String.toList_intercalate, toString]
    · rcases isPredicate_cases hname with hc | he | he
      · exact .comparison hc hls (hw ▸ hrs)
      · exact .equal (.inl he) hls (hw ▸ hrs)
      · exact .equal (.inr he) hls (hw ▸ hrs)
  | arithmetic hname hl hr hw =>
    refine ⟨f, ?_, hfs⟩
    simp [Expr.renderFormula, not_predicate_arithmetic hname] at hf ⊢
    exact hf
  | unary hname hv =>
    refine ⟨f, ?_, hfs⟩
    simp [Expr.renderFormula, unary_not_predicate hname] at hf ⊢
    exact hf
  | extension hkind hv hw =>
    refine ⟨f, ?_, hfs⟩
    simp [Expr.renderFormula, extension_not_predicate] at hf ⊢
    exact hf
  | var name hw => exact ⟨f, by simpa [Expr.renderFormula] using hf, hfs⟩
  | const value hw => exact ⟨f, by simpa [Expr.renderFormula] using hf, hfs⟩
  | extract hv hl hh => exact ⟨f, by simpa [Expr.renderFormula] using hf, hfs⟩
  | concat hl hr => exact ⟨f, by simpa [Expr.renderFormula] using hf, hfs⟩
  | ite hc hcw hy hn hw => exact ⟨f, by simpa [Expr.renderFormula] using hf, hfs⟩
  | select memory ha => exact ⟨f, by simpa [Expr.renderFormula] using hf, hfs⟩

/-! The symbols of a script: valid, and each names one thing. -/

open_private_decls Bap.Symbolic.Expr Bap.Symbolic.Expr escapeChar

private def safeChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

private theorem escapeChar_good {c : Char} (h : (c.isAlphanum || c = '_') = true) : (escapeChar c).toList = [c] := by
  simp [escapeChar, h]

private theorem escapeChar_bad {c : Char} (h : ¬ (c.isAlphanum || c = '_') = true) :
    (escapeChar c).toList = '$' :: Nat.toDigits 10 c.toNat ++ ['$'] := by
  simp only [escapeChar, if_neg h, String.toList_append, toList_toString]
  simp [toString]

private theorem dollar_not_good : ¬ ('$'.isAlphanum || '$' = '_') = true := by decide

private theorem safe_of_digit {c : Char} (h : c.isDigit = true) : safeChar c = true := by
  have : c.isAlphanum = true := by simp [Char.isAlphanum, h]
  simp [safeChar, this]

private theorem safe_escapeChar {c x : Char} (h : x ∈ (escapeChar c).toList) : safeChar x = true := by
  by_cases hg : (c.isAlphanum || c = '_') = true
  · rw [escapeChar_good hg] at h
    obtain rfl := List.mem_singleton.mp h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hg
    simp only [safeChar, Bool.or_eq_true, beq_iff_eq]
    exact .inl hg
  · rw [escapeChar_bad hg] at h
    simp only [List.mem_cons, List.cons_append, List.mem_append, List.not_mem_nil, or_false] at h
    rcases h with rfl | h | rfl
    · decide
    · exact safe_of_digit (digit_of_mem h)
    · decide

private theorem escapeName_toList (name : String) :
    (Expr.escapeName name).toList = name.toList.flatMap fun c => (escapeChar c).toList := by
  simp [Expr.escapeName, String.toList_join, List.flatMap_map]

private theorem safe_escapeName {name : String} {x : Char} (h : x ∈ (Expr.escapeName name).toList) :
    safeChar x = true := by
  rw [escapeName_toList, List.mem_flatMap] at h
  obtain ⟨c, _, hc⟩ := h
  exact safe_escapeChar hc

private theorem escape_inj : ∀ {xs ys : List Char},
    (xs.flatMap fun c => (escapeChar c).toList) = (ys.flatMap fun c => (escapeChar c).toList) → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by
    by_cases hg : (y.isAlphanum || y = '_') = true
    · simp [escapeChar_good hg] at h
    · simp [escapeChar_bad hg] at h
  | x :: xs, [], h => by
    by_cases hg : (x.isAlphanum || x = '_') = true
    · simp [escapeChar_good hg] at h
    · simp [escapeChar_bad hg] at h
  | x :: xs, y :: ys, h => by
    simp only [List.flatMap_cons] at h
    by_cases hx : (x.isAlphanum || x = '_') = true <;> by_cases hy : (y.isAlphanum || y = '_') = true
    · rw [escapeChar_good hx, escapeChar_good hy] at h
      simp only [List.singleton_append, List.cons.injEq] at h
      rw [h.1, escape_inj h.2]
    · rw [escapeChar_good hx, escapeChar_bad hy] at h
      simp only [List.cons_append, List.singleton_append, List.cons.injEq] at h
      rw [h.1] at hx
      exact absurd hx (by decide)
    · rw [escapeChar_bad hx, escapeChar_good hy] at h
      simp only [List.cons_append, List.singleton_append, List.cons.injEq] at h
      rw [← h.1] at hy
      exact absurd hy (by decide)
    · rw [escapeChar_bad hx, escapeChar_bad hy] at h
      simp only [List.cons_append, List.append_assoc, List.singleton_append, List.cons.injEq, true_and] at h
      have hd : ∀ {n : Nat}, '$' ∉ Nat.toDigits 10 n := not_mem_digits (by decide)
      obtain ⟨h1, h2⟩ := split_at hd hd h
      have hc : x = y := Char.toNat_inj.mp (digits_inj h1)
      rw [hc, escape_inj h2]
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf; all_goals omega

/-- Different names are spelled differently. -/
theorem escapeName_injective {a b : String} (h : Expr.escapeName a = Expr.escapeName b) : a = b := by
  have hl := congrArg String.toList h
  rw [escapeName_toList, escapeName_toList] at hl
  exact String.toList_inj.mp (escape_inj hl)

private theorem variableSymbol_toList (name : String) (width : Nat) : (Expr.variableSymbol name width).toList =
    '|' :: ((Expr.escapeName name).toList ++ '!' :: Nat.toDigits 10 width) ++ ['|'] := by
  simp [Expr.variableSymbol, String.toList_append, toList_toString, toString]

private theorem memorySymbol_toList (name : String) (width : Nat) : (Expr.memorySymbol name width).toList =
    '|' :: ((Expr.escapeName name).toList ++ '@' :: Nat.toDigits 10 width) ++ ['|'] := by
  simp [Expr.memorySymbol, String.toList_append, toList_toString, toString]

private theorem not_mem_escape {name : String} {c : Char} (h : safeChar c = false) :
    c ∉ (Expr.escapeName name).toList :=
  fun hm => by rw [safe_escapeName hm] at h; cases h

private theorem symbol_split {a b : List Char} {x y : Char} {c d : List Char}
    (hx : safeChar x = false) (hy : safeChar y = false) (ha : ∀ z ∈ a, safeChar z = true) (hb : ∀ z ∈ b, safeChar z = true)
    (h : (a ++ x :: c) = (b ++ y :: d)) : a = b ∧ x = y ∧ c = d :=
  split_first (fun m => by rw [ha _ m] at hx; cases hx) (fun m => by rw [hb _ m] at hx; cases hx)
    (fun m => by rw [ha _ m] at hy; cases hy) (fun m => by rw [hb _ m] at hy; cases hy) h

private theorem symbol_body {a b : List Char} (h : ('|' :: a ++ ['|']) = ('|' :: b ++ ['|'])) : a = b := by
  simpa using h

theorem variableSymbol_injective {n n' : String} {w w' : Nat} (h : Expr.variableSymbol n w = Expr.variableSymbol n' w') :
    n = n' ∧ w = w' := by
  have hl := congrArg String.toList h
  rw [variableSymbol_toList, variableSymbol_toList] at hl
  obtain ⟨h1, _, h3⟩ := symbol_split (by decide) (by decide) (fun _ => safe_escapeName) (fun _ => safe_escapeName)
    (symbol_body hl)
  exact ⟨escapeName_injective (String.toList_inj.mp h1), digits_inj h3⟩

theorem memorySymbol_injective {n n' : String} {w w' : Nat} (h : Expr.memorySymbol n w = Expr.memorySymbol n' w') :
    n = n' ∧ w = w' := by
  have hl := congrArg String.toList h
  rw [memorySymbol_toList, memorySymbol_toList] at hl
  obtain ⟨h1, _, h3⟩ := symbol_split (by decide) (by decide) (fun _ => safe_escapeName) (fun _ => safe_escapeName)
    (symbol_body hl)
  exact ⟨escapeName_injective (String.toList_inj.mp h1), digits_inj h3⟩

/-- A variable and a memory never share a symbol. -/
theorem variableSymbol_ne_memorySymbol (n n' : String) (w w' : Nat) :
    Expr.variableSymbol n w ≠ Expr.memorySymbol n' w' := by
  intro h
  have hl := congrArg String.toList h
  rw [variableSymbol_toList, memorySymbol_toList] at hl
  obtain ⟨_, h2, _⟩ := symbol_split (by decide) (by decide) (fun _ => safe_escapeName) (fun _ => safe_escapeName)
    (symbol_body hl)
  exact absurd h2 (by decide)

private theorem valid_of_toList {symbol : String} {sep : Char} {name : String} {width : Nat}
    (h : symbol.toList = '|' :: ((Expr.escapeName name).toList ++ sep :: Nat.toDigits 10 width) ++ ['|'])
    (h1 : sep ≠ '|') (h2 : sep ≠ '\\') : ValidSymbol symbol := by
  refine ⟨_, h, ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨not_mem_escape (by decide), h1.symm, not_mem_digits (by decide)⟩
  · simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨not_mem_escape (by decide), h2.symm, not_mem_digits (by decide)⟩

theorem variableSymbol_valid (name : String) (width : Nat) : ValidSymbol (Expr.variableSymbol name width) :=
  valid_of_toList (variableSymbol_toList name width) (by decide) (by decide)

theorem memorySymbol_valid (name : String) (width : Nat) : ValidSymbol (Expr.memorySymbol name width) :=
  valid_of_toList (memorySymbol_toList name width) (by decide) (by decide)

private theorem eraseDups_pairwise [BEq α] [LawfulBEq α] : ∀ (n : Nat) (l : List α), l.length ≤ n →
    l.eraseDups.Pairwise (· ≠ ·) := by
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.pairwise_cons.mpr ⟨?_, ih _ ?_⟩
      · intro b hb
        have := (List.mem_filter.mp (List.mem_eraseDups.mp hb)).2
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at this
        exact fun e => this e.symm
      · have := List.length_filter_le (fun b => !b == a) as
        simp at hl
        omega

/-- The declarations of a script, in order, for names and widths that are all positive. -/
private theorem declareConsts_sorted {rest : List SmtCommand} : ∀ (l : List (String × Nat)) (Γ : SmtSignature),
    l.Pairwise (· ≠ ·) → (∀ v ∈ l, 0 < v.2) →
    (∀ v ∈ l, Expr.variableSymbol v.1 v.2 ∉ Γ.symbols) →
    (∀ Δ : SmtSignature, (∀ x ∈ Γ.constants, x ∈ Δ.constants) → (∀ x ∈ Γ.functions, x ∈ Δ.functions) →
      (∀ v ∈ l, (Expr.variableSymbol v.1 v.2, v.2) ∈ Δ.constants) → ScriptSorted Δ rest) →
    ScriptSorted Γ ((l.map fun v => .declareConst (Expr.variableSymbol v.1 v.2) v.2) ++ rest) := by
  intro l
  induction l with
  | nil => intro Γ _ _ _ h; exact h Γ (fun _ h => h) (fun _ h => h) (by simp)
  | cons v vs ih =>
    intro Γ hp hw hf h
    obtain ⟨hne, hps⟩ := List.pairwise_cons.mp hp
    refine .declareConst (hw v (by simp)) (variableSymbol_valid _ _) (hf v (by simp)) (ih _ hps
      (fun x hx => hw x (by simp [hx])) ?_ ?_)
    · intro x hx hmem
      simp only [SmtSignature.symbols, List.cons_append, List.map_cons, List.mem_cons] at hmem
      rcases hmem with he | hmem
      · obtain ⟨h1, h2⟩ := variableSymbol_injective he
        exact hne x hx (by cases v; cases x; simp_all)
      · exact hf x (by simp [hx]) hmem
    · intro Δ hc hfun hv
      refine h Δ (fun x hx => hc x (by simp [hx])) hfun ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hc _ (by simp)
      · exact hv x hx

private theorem declareFuns_sorted {rest : List SmtCommand} : ∀ (l : List (String × Nat)) (Γ : SmtSignature),
    l.Pairwise (· ≠ ·) → (∀ v ∈ l, 0 < v.2) →
    (∀ v ∈ l, Expr.memorySymbol v.1 v.2 ∉ Γ.symbols) →
    (∀ Δ : SmtSignature, Δ.constants = Γ.constants → (∀ x ∈ Γ.functions, x ∈ Δ.functions) →
      (∀ x ∈ Δ.functions, x ∈ Γ.functions ∨ ∃ m : String × Nat, x.1 = Expr.memorySymbol m.1 m.2) →
      (∀ v ∈ l, (Expr.memorySymbol v.1 v.2, v.2) ∈ Δ.functions) → ScriptSorted Δ rest) →
    ScriptSorted Γ ((l.map fun v => .declareFun (Expr.memorySymbol v.1 v.2) v.2) ++ rest) := by
  intro l
  induction l with
  | nil => intro Γ _ _ _ h; exact h Γ rfl (fun _ h => h) (fun _ h => .inl h) (by simp)
  | cons v vs ih =>
    intro Γ hp hw hf h
    obtain ⟨hne, hps⟩ := List.pairwise_cons.mp hp
    refine .declareFun (hw v (by simp)) (memorySymbol_valid _ _) (hf v (by simp)) (ih _ hps
      (fun x hx => hw x (by simp [hx])) ?_ ?_)
    · intro x hx hmem
      simp only [SmtSignature.symbols, List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hmem
      rcases hmem with hmem | he | hmem
      · exact hf x (by simp [hx]) (by simp [SmtSignature.symbols, List.mem_append]; simpa using .inl (by simpa using hmem))
      · obtain ⟨h1, h2⟩ := memorySymbol_injective he
        exact hne x hx (by cases v; cases x; simp_all)
      · exact hf x (by simp [hx]) (by simp only [SmtSignature.symbols, List.map_append, List.mem_append]; exact .inr hmem)
    · intro Δ hc hfun hsub hv
      refine h Δ hc (fun x hx => hfun x (by simp [hx])) (fun x hx => ?_) ?_
      · rcases hsub x hx with hin | hin
        · rcases List.mem_cons.mp hin with rfl | hin
          · exact .inr ⟨v, rfl⟩
          · exact .inl hin
        · exact .inr hin
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfun _ (by simp)
      · exact hv x hx

private theorem asserts_sorted (Γ : SmtSignature) : ∀ (cs : List Expr), (∀ c ∈ cs, WellSorted c ∧ Declares Γ c) →
    ∃ ts : List SmtTerm, ts.map SmtTerm.print = cs.map Expr.renderFormula ∧
      ScriptSorted Γ (ts.map .assert ++ [.checkSat]) := by
  intro cs
  induction cs with
  | nil => intro _; exact ⟨[], rfl, .checkSat (.nil _)⟩
  | cons c cs ih =>
    intro h
    obtain ⟨hw, hd⟩ := h c (by simp)
    obtain ⟨t, hp, hs⟩ := renderFormula_hasSort hw hd
    obtain ⟨ts, hps, hss⟩ := ih fun x hx => h x (by simp [hx])
    exact ⟨t :: ts, by simp [hp, hps], .assert hs hss⟩

/-- What an expression reads is all positive, when it is well sorted. -/
private theorem reads_positive {e : Expr} (h : WellSorted e) :
    (∀ v ∈ e.vars, 0 < v.2) ∧ ∀ m ∈ e.memories, 0 < m.2 := by
  induction h with
  | var name hw => exact ⟨by simpa [Expr.vars] using hw, by simp [Expr.memories]⟩
  | const value hw => exact ⟨by simp [Expr.vars], by simp [Expr.memories]⟩
  | arithmetic _ _ _ _ ihl ihr | predicate _ _ _ _ ihl ihr =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp [Expr.vars] at hv
      exact hv.elim (ihl.1 _) (ihr.1 _)
    · simp [Expr.memories] at hv
      exact hv.elim (ihl.2 _) (ihr.2 _)
  | unary _ _ ih | extension _ _ _ ih =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp [Expr.vars] at hv
      exact ih.1 _ hv
    · simp [Expr.memories] at hv
      exact ih.2 _ hv
  | extract _ _ _ ih => exact ⟨by simpa [Expr.vars] using ih.1, by simpa [Expr.memories] using ih.2⟩
  | concat _ _ ihl ihr =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp [Expr.vars] at hv
      exact hv.elim (ihl.1 _) (ihr.1 _)
    · simp [Expr.memories] at hv
      exact hv.elim (ihl.2 _) (ihr.2 _)
  | ite _ _ _ _ _ ihc ihy ihn =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · simp [Expr.vars] at hv
      rcases hv with hv | hv | hv
      · exact ihc.1 _ hv
      · exact ihy.1 _ hv
      · exact ihn.1 _ hv
    · simp [Expr.memories] at hv
      rcases hv with hv | hv | hv
      · exact ihc.2 _ hv
      · exact ihy.2 _ hv
      · exact ihn.2 _ hv
  | @select memory address ha ih =>
    refine ⟨by simpa [Expr.vars] using ih.1, fun v hv => ?_⟩
    simp only [Expr.memories, List.mem_eraseDups, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha.width_pos
    · exact ih.2 _ hv

/-- The script of well-sorted constraints is well sorted: the string `renderScript` returns is the printing of a script
that declares each symbol once and before its use, in a logic that has them, and asserts only formulas. -/
theorem renderScript_wellSorted {constraints : List Expr} (h : ∀ c ∈ constraints, WellSorted c) :
    ∃ script : List SmtCommand, String.intercalate "\n" (script.map SmtCommand.print) = renderScript constraints ∧
      WellSortedScript script := by
  let variables := (constraints.flatMap Expr.vars).eraseDups
  let memories := (constraints.flatMap Expr.memories).eraseDups
  have hvars : ∀ c ∈ constraints, ∀ v ∈ c.vars, v ∈ variables := fun c hc v hv =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨c, hc, hv⟩)
  have hmems : ∀ c ∈ constraints, ∀ m ∈ c.memories, m ∈ memories := fun c hc m hm =>
    List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨c, hc, hm⟩)
  have hvpos : ∀ v ∈ variables, 0 < v.2 := by
    intro v hv
    obtain ⟨c, hc, hin⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hv)
    exact (reads_positive (h c hc)).1 v hin
  have hmpos : ∀ m ∈ memories, 0 < m.2 := by
    intro m hm
    obtain ⟨c, hc, hin⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hm)
    exact (reads_positive (h c hc)).2 m hin
  -- The assertions under any signature that has the declarations.
  have hasserts : ∀ Δ : SmtSignature, (∀ v ∈ variables, (Expr.variableSymbol v.1 v.2, v.2) ∈ Δ.constants) →
      (∀ m ∈ memories, (Expr.memorySymbol m.1 m.2, m.2) ∈ Δ.functions) →
      ∃ ts : List SmtTerm, ts.map SmtTerm.print = constraints.map Expr.renderFormula ∧
        ScriptSorted Δ (ts.map .assert ++ [.checkSat]) := by
    intro Δ hv hm
    exact asserts_sorted Δ constraints fun c hc =>
      ⟨h c hc, fun v hin => hv v (hvars c hc v hin), fun m hin => hm m (hmems c hc m hin)⟩
  -- The terms don't depend on the signature's order: fix them against the full signature.
  let full : SmtSignature := {
    constants := variables.map fun v => (Expr.variableSymbol v.1 v.2, v.2)
    functions := memories.map fun m => (Expr.memorySymbol m.1 m.2, m.2) }
  have hmemv : ∀ v ∈ variables, (Expr.variableSymbol v.1 v.2, v.2) ∈ full.constants := fun v hv =>
    List.mem_map.mpr ⟨v, hv, rfl⟩
  have hmemm : ∀ m ∈ memories, (Expr.memorySymbol m.1 m.2, m.2) ∈ full.functions := fun m hm =>
    List.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨ts, hts, hsorted⟩ : ∃ ts : List SmtTerm, ts.map SmtTerm.print = constraints.map Expr.renderFormula ∧
      ∀ Δ : SmtSignature, (∀ x ∈ full.constants, x ∈ Δ.constants) → (∀ x ∈ full.functions, x ∈ Δ.functions) →
        ScriptSorted Δ (ts.map .assert ++ [.checkSat]) := by
    obtain ⟨ts, hp, hs⟩ := hasserts full hmemv hmemm
    refine ⟨ts, hp, fun Δ hc hf => ?_⟩
    clear hp
    induction ts with
    | nil => exact .checkSat (.nil _)
    | cons t rest ih =>
      cases hs with
      | assert ht hr => exact .assert (ht.weaken hc hf) (ih hr)
  refine ⟨.setLogic (if memories.isEmpty then "QF_BV" else "QF_UFBV") ::
    ((memories.map fun m => .declareFun (Expr.memorySymbol m.1 m.2) m.2) ++
    ((variables.map fun v => .declareConst (Expr.variableSymbol v.1 v.2) v.2) ++
    (ts.map .assert ++ [.checkSat]))), ?_, ?_, ?_⟩
  · simp only [renderScript, List.map_cons, List.map_append, List.map_map]
    have hassert : (ts.map fun t => (SmtCommand.assert t).print) =
        constraints.map fun c => s!"(assert {c.renderFormula})" := by
      have := congrArg (List.map fun f => s!"(assert {f})") hts
      simpa [List.map_map, Function.comp_def, SmtCommand.print] using this
    have hcomp : (ts.map (SmtCommand.print ∘ SmtCommand.assert)) = ts.map fun t => (SmtCommand.assert t).print := rfl
    simp only [hcomp, hassert]
    congr 1
    simp [SmtCommand.print, Function.comp_def, variables, memories]
  · refine declareFuns_sorted memories {} (eraseDups_pairwise _ _ (Nat.le_refl _)) hmpos (by simp [SmtSignature.symbols]) ?_
    intro Δ hconst hfun hsub hm
    refine declareConsts_sorted variables Δ (eraseDups_pairwise _ _ (Nat.le_refl _)) hvpos ?_ ?_
    · intro v _ hmem
      simp only [SmtSignature.symbols, List.map_append, List.mem_append, hconst] at hmem
      rcases hmem with hmem | hmem
      · simp at hmem
      · obtain ⟨x, hx, he⟩ := List.mem_map.mp hmem
        rcases hsub x hx with hin | ⟨m, hm'⟩
        · cases hin
        · exact variableSymbol_ne_memorySymbol _ _ _ _ (he.symm.trans hm')
    · intro Θ hc hf hv
      exact hsorted Θ (fun x hx => by
        obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hx
        exact hv v hv') (fun x hx => by
        obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hx
        exact hf _ (hm m hm'))
  · split
    · next he =>
      refine .inr ⟨rfl, fun symbol width hmem => ?_⟩
      have hnil : memories = [] := by simpa using he
      simp [hnil] at hmem
    · exact .inl rfl

/-! The executor only builds well-sorted expressions. -/

/-- A memory holding well-sorted bytes at well-sorted addresses. -/
inductive MemorySorted : Bap.Symbolic.Memory → Prop where
  | plain (name cells) : (∀ cell ∈ cells, WellSorted cell.1 ∧ WellSorted cell.2 ∧ cell.2.width = 8) →
      MemorySorted ⟨name, none, cells⟩
  | branch (name) {condition yes no cells} : WellSorted condition → condition.width = 1 → MemorySorted yes →
      MemorySorted no → (∀ cell ∈ cells, WellSorted cell.1 ∧ WellSorted cell.2 ∧ cell.2.width = 8) →
      MemorySorted ⟨name, some (condition, yes, no), cells⟩

theorem MemorySorted.cells {memory : Bap.Symbolic.Memory} (h : MemorySorted memory) :
    ∀ cell ∈ memory.cells, WellSorted cell.1 ∧ WellSorted cell.2 ∧ cell.2.width = 8 := by
  cases h <;> assumption

/-- A state whose registers and memories hold such expressions. -/
structure StateSorted (s : State) : Prop where
  env : ∀ entry ∈ s.env, WellSorted entry.2
  memories : ∀ entry ∈ s.memories, MemorySorted entry.2

/-- Addresses compared by a guard have one width: addresses of different ones are never the same location. -/
theorem width_eq_of_not_distinct {a b : Expr} (h : Memory.definitelyDistinct a b = false) : a.width = b.width := by
  have hgeneral : (a.width != b.width || ((Memory.baseOffset a).2 != (Memory.baseOffset b).2 &&
      Expr.structuralEq (Memory.baseOffset a).1 (Memory.baseOffset b).1)) = false → a.width = b.width := by
    intro hg
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hg
    exact hg.1
  cases a <;> cases b <;> first | exact hgeneral h | skip
  simp only [Memory.definitelyDistinct, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem sorted_readCells {initial address : Expr} {cells : List (Expr × Expr)} (hi : WellSorted initial)
    (hiw : initial.width = 8) (ha : WellSorted address)
    (h : ∀ cell ∈ cells, WellSorted cell.1 ∧ WellSorted cell.2 ∧ cell.2.width = 8) :
    WellSorted (Memory.readCells initial address cells) ∧ (Memory.readCells initial address cells).width = 8 := by
  induction cells with
  | nil => exact ⟨hi, hiw⟩
  | cons cell rest ih =>
    obtain ⟨c1, c2, c3⟩ := h cell (by simp)
    obtain ⟨r1, r2⟩ := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [Memory.readCells]
    split
    · exact ⟨c2, c3⟩
    · split
      · exact ⟨r1, r2⟩
      · next hd =>
        have hw := width_eq_of_not_distinct (by simpa using hd)
        exact ⟨.ite (.predicate (by decide) c1 ha hw) rfl c2 r1 (by rw [c3, r2]), c3⟩

private theorem sorted_readByte {memory : Bap.Symbolic.Memory} {address : Expr} (h : MemorySorted memory)
    (ha : WellSorted address) : WellSorted (memory.readByte address) ∧ (memory.readByte address).width = 8 := by
  have hinit : WellSorted (Memory.readInitial memory address) ∧ (Memory.readInitial memory address).width = 8 := by
    induction h with
    | plain name cells _ => exact ⟨.select _ ha, rfl⟩
    | branch name hc hcw hy hn hcells ihy ihn =>
      have y := sorted_readCells ihy.1 ihy.2 ha hy.cells
      have n := sorted_readCells ihn.1 ihn.2 ha hn.cells
      exact ⟨.ite hc hcw y.1 n.1 (by rw [y.2, n.2]), y.2⟩
  exact sorted_readCells hinit.1 hinit.2 ha h.cells

private theorem sorted_offsetAddress {address : Expr} (ha : WellSorted address) (offset : Nat) :
    WellSorted (offsetAddress address offset) := by
  unfold offsetAddress
  split
  · exact .const _ (by simpa [Expr.width] using ha.width_pos)
  · split
    · exact ha
    · exact .arithmetic (by decide) ha (.const _ ha.width_pos) rfl

private theorem sorted_chain {ordered : List Expr} (h : ∀ b ∈ ordered, WellSorted b) (hne : ordered ≠ []) :
    WellSorted (chainBytes ordered) := by
  have hchain : ∀ (bytes : List Expr) (first : Expr), WellSorted first → (∀ b ∈ bytes, WellSorted b) →
      WellSorted (bytes.foldl (fun result byte => .concat result byte) first) := by
    intro bytes
    induction bytes with
    | nil => intro first hf _; exact hf
    | cons b rest ih =>
      intro first hf hb
      exact ih _ (.concat hf (hb b (by simp))) fun x hx => hb x (by simp [hx])
  cases ordered with
  | nil => exact absurd rfl hne
  | cons first rest => exact hchain _ _ (h first (by simp)) fun x hx => h x (by simp [hx])

private theorem sorted_readValue {memory : Bap.Symbolic.Memory} {address : Expr} (h : MemorySorted memory)
    (ha : WellSorted address) (endian : Endian) {size : Nat} (hz : size ≠ 0) :
    WellSorted (readValue memory address endian size) := by
  refine sorted_chain ?_ ?_
  · intro b hb
    simp only [Bap.Symbolic.Memory.readBytes] at hb
    split at hb <;> (try rw [List.mem_reverse] at hb) <;> obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb <;>
      exact (sorted_readByte h (sorted_offsetAddress ha _)).1
  · intro he
    have := length_readBytes memory address endian size
    rw [he] at this
    exact hz this.symm

private theorem sorted_byteAt {value : Expr} (hv : WellSorted value) {size offset : Nat} (hw : value.width = size * 8)
    (ho : offset < size) : WellSorted (byteAt value offset) ∧ (byteAt value offset).width = 8 := by
  refine ⟨.extract hv (by omega) ?_, by simp only [byteAt, Expr.width]; omega⟩
  have : (offset + 1) * 8 ≤ size * 8 := Nat.mul_le_mul_right 8 ho
  rw [hw, Nat.add_mul] at *
  omega

private theorem sorted_writeByte {memory : Bap.Symbolic.Memory} {address value : Expr} (h : MemorySorted memory)
    (ha : WellSorted address) (hv : WellSorted value) (hw : value.width = 8) :
    MemorySorted (memory.writeByte address value) := by
  have hc : ∀ cell ∈ (memory.writeByte address value).cells, WellSorted cell.1 ∧ WellSorted cell.2 ∧ cell.2.width = 8 := by
    intro cell hcell
    rcases List.mem_cons.mp hcell with rfl | hcell
    · exact ⟨ha, hv, hw⟩
    · exact h.cells cell (List.mem_filter.mp hcell).1
  cases h with
  | plain name cells _ => exact .plain _ _ hc
  | branch name h1 h2 hy hn _ => exact .branch _ h1 h2 hy hn hc

private theorem sorted_write {memory : Bap.Symbolic.Memory} {address value : Expr} (h : MemorySorted memory)
    (ha : WellSorted address) (hv : WellSorted value) (endian : Endian) {size : Nat} (hw : value.width = size * 8) :
    MemorySorted (memory.write address value endian size) := by
  rw [write_eq_prefix]
  have : ∀ k, k ≤ size → MemorySorted (writePrefix memory address value endian size k) := by
    intro k
    induction k with
    | zero => intro _; exact h
    | succ k ih =>
      intro hk
      rw [writePrefix_succ]
      have hindex : (if endian = Bap.Endian.little then k else size - 1 - k) < size := by split <;> omega
      obtain ⟨b1, b2⟩ := sorted_byteAt hv hw hindex
      exact sorted_writeByte (ih (by omega)) (sorted_offsetAddress ha _) b1 b2
  exact this size (Nat.le_refl _)

private theorem sorted_binary (op : Bil.BinOp) {l r : Expr} (hl : WellSorted l) (hr : WellSorted r)
    (hw : l.width = r.width) : WellSorted (binary op l r) := by
  rcases binary_cases op l r with h | ⟨a, av, b, bv, c, cv, rfl, rfl, hf, h⟩
  · rw [h]
    cases op
    all_goals first
      | exact .arithmetic (by decide) hl hr hw
      | exact .predicate (by decide) hl hr hw
  · rw [h]
    have hpos : 0 < a := hl.width_pos
    simp only [Expr.width] at hw
    subst hw
    obtain ⟨v', hv', hb⟩ := evalBin_same op av bv
    rw [hv'] at hf
    cases hf
    have hpos' : 0 < (bilBinary op av bv).1 := by cases op <;> first | exact hpos | exact Nat.one_pos
    exact .const _ hpos'

private theorem sorted_evalCast {kind : Bil.Cast} {width : Nat} {value result : Expr} (hv : WellSorted value)
    (h : evalCast kind width value = .ok result) : WellSorted result := by
  unfold evalCast at h
  split at h
  · cases h
  · next hz =>
    have hvp := hv.width_pos
    split at h
    · split at h
      · cases h
      · next hle =>
        cases h
        exact .extract hv (by omega) (by omega)
    all_goals
      simp only at h
      split at h <;> cases h
      · exact .extract hv (by omega) (by omega)
      · refine .extension (by first | exact .inr rfl | exact .inl rfl | (split <;> simp)) hv (by omega)

/-- Every expression and memory the evaluator builds from well-sorted parts is well sorted. -/
theorem eval_sorted (e : Bil.Exp) :
    (∀ {s : State} {x : Expr}, StateSorted s → evalExp s e = .ok x → WellSorted x) ∧
      (∀ {s : State} {m : Bap.Symbolic.Memory}, StateSorted s → evalMemory s e = .ok m → MemorySorted m) := by
  induction e with
  | int value =>
    refine ⟨fun _ h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp] at h
    split at h
    · cases h
    · next hz =>
      cases h
      exact .const _ (Nat.pos_of_ne_zero hz)
  | var var =>
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp] at h
      rcases (lookup_ok h).2 with hg | ⟨_, rfl, hw⟩
      · exact hs.env _ (get_mem hg)
      · exact .var _ (Nat.pos_of_ne_zero hw)
    · simp only [evalMemory] at h
      split at h
      · cases h
        unfold memoryOf
        split
        · next memory heq => exact hs.memories _ (get_mem heq)
        · exact .plain _ _ (fun _ hc => by cases hc)
      · cases h
  | load memory address endian size ihm iha =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨m, hm, a, ha, h⟩ := h
    obtain ⟨hz, rfl⟩ := read_ok h
    exact sorted_readValue (ihm.2 hs hm) (iha.1 hs ha) endian hz
  | store memory address value endian size ihm iha ihv =>
    refine ⟨fun _ h => by simp [evalExp] at h, fun hs h => ?_⟩
    simp only [evalMemory, bind_ok] at h
    obtain ⟨m, hm, a, ha, v, hv, h⟩ := h
    split at h
    · cases h
    · split at h
      · cases h
      · next hw =>
        split at h
        · cases h
        · cases h
          exact sorted_write (ihm.2 hs hm) (iha.1 hs ha) (ihv.1 hs hv) _ (Decidable.not_not.mp hw)
  | bin op left right ihl ihr =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hr, h⟩ := h
    split at h
    · cases h
    · next hw =>
      cases h
      exact sorted_binary op (ihl.1 hs hl) (ihr.1 hs hr) (Decidable.not_not.mp hw)
  | un op value ih =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨v, hv, h⟩ := h
    cases h
    exact .unary (by cases op <;> simp) (ih.1 hs hv)
  | cast kind width value ih =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨v, hv, h⟩ := h
    exact sorted_evalCast (ih.1 hs hv) h
  | letIn var value body ihv ihb =>
    have hmem : ∀ {s : State} {m : Bap.Symbolic.Memory}, StateSorted s → MemorySorted m →
        StateSorted { s with memories := (var, m) :: s.memories } := by
      intro s m hs hm
      exact ⟨hs.env, fun entry he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hm
        · exact hs.memories entry he⟩
    have hbits : ∀ {s : State} {x : Expr}, StateSorted s → WellSorted x →
        StateSorted { s with env := (var, x) :: s.env } := by
      intro s x hs hx
      exact ⟨fun entry he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hs.env entry he, hs.memories⟩
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp] at h
      split at h
      · obtain ⟨m, hm, h⟩ := bind_ok.mp h
        exact ihb.1 (hmem hs (ihv.2 hs hm)) h
      · obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact ihb.1 (hbits hs (ihv.1 hs hx)) h
    · simp only [evalMemory] at h
      split at h
      · obtain ⟨m, hm, h⟩ := bind_ok.mp h
        exact ihb.2 (hmem hs (ihv.2 hs hm)) h
      · obtain ⟨x, hx, h⟩ := bind_ok.mp h
        exact ihb.2 (hbits hs (ihv.1 hs hx)) h
  | ite condition yes no ihc ihy ihn =>
    refine ⟨fun hs h => ?_, fun hs h => ?_⟩
    · simp only [evalExp, bind_ok] at h
      obtain ⟨c, hc, y, hy, n, hn, h⟩ := h
      split at h
      · cases h
      · next hcw =>
        split at h
        · cases h
        · next hw =>
          cases h
          exact .ite (ihc.1 hs hc) (Decidable.not_not.mp hcw) (ihy.1 hs hy) (ihn.1 hs hn) (Decidable.not_not.mp hw)
    · simp only [evalMemory, bind_ok] at h
      obtain ⟨c, hc, y, hy, n, hn, h⟩ := h
      split at h
      · cases h
      · next hcw =>
        have y1 := ihy.2 hs hy
        have n1 := ihn.2 hs hn
        split at h
        · cases h; exact y1
        · cases h; exact n1
        · cases h
          exact .branch _ (ihc.1 hs hc) (Decidable.not_not.mp hcw) y1 n1 (fun _ hc => by cases hc)
  | extract high low value ih =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨x, hx, h⟩ := h
    split at h
    · cases h
    · next hl =>
      split at h
      · cases h
      · next hh =>
        cases h
        exact .extract (ih.1 hs hx) (by omega) (by omega)
  | concat left right ihl ihr =>
    refine ⟨fun hs h => ?_, fun _ h => by simp [evalMemory] at h⟩
    simp only [evalExp, bind_ok] at h
    obtain ⟨l, hl, r, hr, h⟩ := h
    cases h
    exact .concat (ihl.1 hs hl) (ihr.1 hs hr)
  | unknown message typ =>
    refine ⟨fun _ h => ?_, fun _ h => ?_⟩
    · simp only [evalExp] at h
      split at h
      · cases h
      · next hz =>
        cases h
        exact .var _ (Nat.pos_of_ne_zero hz)
    · simp only [evalMemory] at h
      cases h
      exact .plain _ _ (fun _ hc => by cases hc)

/-- From the empty state, every path condition is well sorted. -/
theorem run_constraints_sorted {program : Bil.Program} {f : Nat} {rs : List Result}
    (h : run program {} f = .ok rs) : ∀ r ∈ rs, ∀ c ∈ r.state.constraints, WellSorted c := by
  have hinv : StepInvariant fun s => StateSorted s ∧ ∀ c ∈ s.constraints, WellSorted c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s e x he hw hs
      have hx := (eval_sorted e).1 hs.1 he
      have add : ∀ {y : Expr}, WellSorted y → StateSorted (withConstraint s y) ∧
          ∀ c ∈ (withConstraint s y).constraints, WellSorted c := by
        intro y hy
        refine ⟨⟨hs.1.env, hs.1.memories⟩, fun c hc => ?_⟩
        simp only [withConstraint, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact hs.2 c hc
        · exact hy
      refine ⟨add (by rw [eqOne_of_width_one hw]; exact hx), add ?_⟩
      exact .predicate (by decide) hx (.const _ hx.width_pos) rfl
    · exact fun _ _ hs => ⟨⟨hs.1.env, hs.1.memories⟩, hs.2⟩
    · intro s var value x hs hx
      exact ⟨⟨fun entry he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact (eval_sorted value).1 hs.1 hx
        · exact hs.1.env entry he, hs.1.memories⟩, hs.2⟩
    · intro s var value m hs hm
      exact ⟨⟨hs.1.env, fun entry he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact (eval_sorted value).2 hs.1 hm
        · exact hs.1.memories entry he⟩, hs.2⟩
  intro r hr
  exact ((execute_preserves hinv f).2 {} program rs
    ⟨⟨fun _ he => (by cases he), fun _ he => (by cases he)⟩, fun _ he => (by cases he)⟩ h r hr).2

/-- The headline for sorts: the script of each path of `bap symbolic`, on any program, is well sorted, with nothing of
zero width anywhere in it. -/
theorem run_script_wellSorted {program : Bil.Program} {f : Nat} {rs : List Result} (h : run program {} f = .ok rs) :
    ∀ r ∈ rs, ∃ script : List SmtCommand,
      String.intercalate "\n" (script.map SmtCommand.print) = renderScript r.state.constraints ∧ WellSortedScript script :=
  fun r hr => renderScript_wellSorted (run_constraints_sorted h r hr)

end Bap.Proofs.Symbolic
