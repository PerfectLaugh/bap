import Bap.Bil.Binary

/-! What the binary form of BIL writes, it reads back. Each lemma has one form: if what was written up to and including a value is
a prefix of the file, then what was written before it is too, and reading from there gives the value and the position after it.
So a record is read back by taking its fields from the last one to the first. -/

namespace Bap.Proofs.Binary

open Bap Bap.Binary Bap.Bil

/-- `first` is the start of `second`. -/
def Prefix (first second : ByteArray) : Prop := ∃ tail, second = first ++ tail

theorem Prefix.refl (data : ByteArray) : Prefix data data := ⟨ByteArray.empty, by simp⟩

theorem Prefix.trans {a b c : ByteArray} (h1 : Prefix a b) (h2 : Prefix b c) : Prefix a c := by
  obtain ⟨t1, rfl⟩ := h1
  obtain ⟨t2, rfl⟩ := h2
  exact ⟨t1 ++ t2, by simp [ByteArray.append_assoc]⟩

theorem Prefix.size_le {a b : ByteArray} (h : Prefix a b) : a.size ≤ b.size := by
  obtain ⟨t, rfl⟩ := h
  simp [ByteArray.size_append]

private theorem push_eq (out : ByteArray) (value : UInt8) : out.push value = out ++ [value].toByteArray := by
  simp

theorem Prefix.of_push {out data : ByteArray} {value : UInt8} (h : Prefix (out.push value) data) : Prefix out data := by
  rw [push_eq] at h
  exact Prefix.trans ⟨_, rfl⟩ h

theorem Prefix.byte {out data : ByteArray} {value : UInt8} (h : Prefix (out.push value) data) :
    ∃ hs : out.size < data.size, data[out.size] = value := by
  have hl := h.size_le
  rw [ByteArray.size_push] at hl
  refine ⟨by omega, ?_⟩
  obtain ⟨tail, rfl⟩ := h
  rw [ByteArray.getElem_append_left (hlt := by simp [ByteArray.size_push])]
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_push]
  exact Array.getElem_push_eq

/-! ### Numbers -/

theorem getByte_push {out data : ByteArray} {value : UInt8} (h : Prefix (out.push value) data) :
    Prefix out data ∧ getByte data out.size = some (value, (out.push value).size) := by
  obtain ⟨hs, hb⟩ := h.byte
  refine ⟨h.of_push, ?_⟩
  simp [getByte, hs, hb, ByteArray.size_push]

private theorem toNat_low {value : Nat} (h : value < 128) : (value.toUInt8).toNat = value := by
  simp [Nat.toUInt8]
  omega

private theorem toNat_high (value : Nat) : ((value % 128 + 128).toUInt8).toNat = value % 128 + 128 := by
  simp [Nat.toUInt8]
  omega

private theorem getNatFrom_putNat (data : ByteArray) (value : Nat) :
    ∀ (out : ByteArray) (acc scale : Nat), Prefix (putNat out value) data →
      Prefix out data ∧ getNatFrom data out.size acc scale = some (acc + value * scale, (putNat out value).size) := by
  induction value using Nat.strongRecOn with
  | _ value ih =>
    intro out acc scale h
    rw [putNat] at h
    by_cases hv : value < 128
    · simp only [hv, ↓reduceIte] at h
      obtain ⟨hs, hb⟩ := h.byte
      refine ⟨h.of_push, ?_⟩
      rw [putNat, getNatFrom]
      simp [hs, hb, toNat_low hv, hv, ByteArray.size_push]
    · simp only [hv, ↓reduceIte] at h
      obtain ⟨hp, hr⟩ := ih (value / 128) (by omega) _ (acc + (value % 128) * scale) (scale * 128) h
      obtain ⟨hs, hb⟩ := hp.byte
      refine ⟨hp.of_push, ?_⟩
      rw [putNat, getNatFrom]
      have hsize : out.size + 1 = (out.push (value % 128 + 128).toUInt8).size := by simp [ByteArray.size_push]
      have hhigh : ¬ (value % 128 + 128 < 128) := by omega
      simp only [hs, ↓reduceDIte, hb, toNat_high, hhigh, hv, ↓reduceIte, Nat.add_sub_cancel, hsize, hr]
      have hd : value = 128 * (value / 128) + value % 128 := (Nat.div_add_mod value 128).symm
      congr 2
      grind

theorem getNat_putNat {out data : ByteArray} {value : Nat} (h : Prefix (putNat out value) data) :
    Prefix out data ∧ getNat data out.size = some (value, (putNat out value).size) := by
  obtain ⟨hp, hr⟩ := getNatFrom_putNat data value out 0 1 h
  refine ⟨hp, ?_⟩
  rw [putNat] at h hr ⊢
  by_cases hv : value < 128
  · simp only [hv, ↓reduceIte] at h ⊢
    obtain ⟨hs, hb⟩ := h.byte
    simp [getNat, hs, hb, toNat_low hv, hv, ByteArray.size_push]
  · simp only [hv, ↓reduceIte] at h hr ⊢
    obtain ⟨hp', hr'⟩ := getNatFrom_putNat data (value / 128) _ (value % 128) 128 h
    obtain ⟨hs, hb⟩ := hp'.byte
    have hsize : out.size + 1 = (out.push (value % 128 + 128).toUInt8).size := by simp [ByteArray.size_push]
    have hhigh : ¬ (value % 128 + 128 < 128) := by omega
    simp only [getNat, hs, ↓reduceDIte, hb, toNat_high, hhigh, ↓reduceIte, Nat.add_sub_cancel, hsize, hr']
    have hd : value = 128 * (value / 128) + value % 128 := (Nat.div_add_mod value 128).symm
    congr 2
    omega

theorem getBool_putBool {out data : ByteArray} {value : Bool} (h : Prefix (putBool out value) data) :
    Prefix out data ∧ getBool data out.size = some (value, (putBool out value).size) := by
  cases value <;> simp only [putBool] at h ⊢ <;> obtain ⟨hp, hr⟩ := getByte_push h <;>
    · simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
      exact ⟨hp, by simp only [getBool, hr]⟩

/-! ### Bytes and text -/

theorem getBytes_putBytes {out data bytes : ByteArray} (h : Prefix (putBytes out bytes) data) :
    Prefix out data ∧ getBytes data out.size = some (bytes, (putBytes out bytes).size) := by
  simp only [putBytes] at h ⊢
  have hn : Prefix (putNat out bytes.size) data := Prefix.trans ⟨_, rfl⟩ h
  obtain ⟨hp, hr⟩ := getNat_putNat hn
  refine ⟨hp, ?_⟩
  have hl := h.size_le
  rw [ByteArray.size_append] at hl ⊢
  obtain ⟨tail, htail⟩ := h
  have hx : data.extract (putNat out bytes.size).size ((putNat out bytes.size).size + bytes.size) = bytes := by
    have hx := ByteArray.extract_append_size_add (a := putNat out bytes.size) (b := bytes ++ tail) (i := 0) (j := bytes.size)
    simp only [Nat.add_zero] at hx
    rw [htail, ByteArray.append_assoc, hx, ByteArray.extract_append_eq_left (hi := rfl)]
  simp [getBytes, hr, hl, hx]

theorem getText_putText {out data : ByteArray} {text : String} (h : Prefix (putText out text) data) :
    Prefix out data ∧ getText data out.size = some (text, (putText out text).size) := by
  obtain ⟨hp, hr⟩ := getBytes_putBytes h
  refine ⟨hp, ?_⟩
  have hv : String.fromUTF8? text.toUTF8 = some text := by
    simp [String.fromUTF8?]
    exact ⟨text.isValidUTF8, rfl⟩
  simp only [getText, hr, putText, bind, Option.bind, hv]

/-! ### Lists -/

/-- What `put` writes on any start, `get` reads back, on this file. -/
def Reads {α : Type} (get : Nat → Option (α × Nat)) (put : ByteArray → α → ByteArray) (data : ByteArray) (value : α) : Prop :=
  ∀ out, Prefix (put out value) data → Prefix out data ∧ get out.size = some (value, (put out value).size)

theorem getItems_putItems {α : Type} {get : Nat → Option (α × Nat)} {put : ByteArray → α → ByteArray} {data : ByteArray}
    {items : List α} (hi : ∀ item ∈ items, Reads get put data item) :
    ∀ (out : ByteArray) (done : Array α), Prefix (putItems put out items) data →
      Prefix out data ∧ getItems get items.length out.size done = some (done ++ items.toArray, (putItems put out items).size) := by
  induction items with
  | nil =>
    intro out done h
    exact ⟨h, by simp [putItems, getItems]⟩
  | cons item rest ih =>
    intro out done h
    simp only [putItems] at h ⊢
    obtain ⟨hp, hr⟩ := ih (fun other hm => hi other (List.mem_cons_of_mem _ hm)) _ (done.push item) h
    obtain ⟨hq, hg⟩ := hi item List.mem_cons_self _ hp
    refine ⟨hq, ?_⟩
    simp [getItems, hg, hr]

theorem getArray_putList {α : Type} {get : Nat → Option (α × Nat)} {put : ByteArray → α → ByteArray} {data : ByteArray}
    {items : List α} (hi : ∀ item ∈ items, Reads get put data item) {out : ByteArray} (h : Prefix (putList put out items) data) :
    Prefix out data ∧ getArray get data out.size = some (items.toArray, (putList put out items).size) := by
  simp only [putList] at h ⊢
  obtain ⟨hp, hr⟩ := getItems_putItems hi _ #[] h
  obtain ⟨hq, hn⟩ := getNat_putNat hp
  refine ⟨hq, ?_⟩
  simp [getArray, hn, hr]

theorem getList_putList {α : Type} {get : Nat → Option (α × Nat)} {put : ByteArray → α → ByteArray} {data : ByteArray}
    {items : List α} (hi : ∀ item ∈ items, Reads get put data item) {out : ByteArray} (h : Prefix (putList put out items) data) :
    Prefix out data ∧ getList get data out.size = some (items, (putList put out items).size) := by
  obtain ⟨hq, hr⟩ := getArray_putList hi h
  refine ⟨hq, ?_⟩
  simp [getList, hr]

theorem getOption_putOption {α : Type} {get : Nat → Option (α × Nat)} {put : ByteArray → α → ByteArray} {data : ByteArray}
    {value : Option α} (hi : ∀ item, value = some item → Reads get put data item) {out : ByteArray} (h : Prefix (putOption put out value) data) :
    Prefix out data ∧ getOption get data out.size = some (value, (putOption put out value).size) := by
  cases value with
  | none =>
    obtain ⟨hp, hr⟩ := getByte_push (out := out) (value := 0) h
    exact ⟨hp, by simp only [getOption, hr, putOption]⟩
  | some item =>
    obtain ⟨hq, hg⟩ := hi item rfl _ h
    obtain ⟨hp, hr⟩ := getByte_push hq
    exact ⟨hp, by simp only [getOption, hr, hg, putOption]⟩

/-! ### Tables -/

/-- What `putAt` writes `getRef` reads back, with the items of the table in the file, wherever it looked. -/
theorem getRef_putAt {α : Type} [BEq α] {get : Nat → Option (α × Nat)} {put : ByteArray → α → ByteArray} {data : ByteArray}
    (heq : ∀ first second : α, (first == second) = true → first = second) {items : Array α} {position : Nat} {value : α}
    (hi : Reads get put data value) {out : ByteArray} (h : Prefix (putAt put items position out value) data) :
    Prefix out data ∧ getRef get items data out.size = some (value, (putAt put items position out value).size) := by
  have inline : Prefix (put (putNat out 0) value) data →
      Prefix out data ∧ getRef get items data out.size = some (value, (put (putNat out 0) value).size) := by
    intro h
    obtain ⟨hq, hg⟩ := hi _ h
    obtain ⟨hp, hn⟩ := getNat_putNat hq
    exact ⟨hp, by simp only [getRef, hn, hg]⟩
  simp only [putAt] at h ⊢
  cases hf : items[position]? with
  | none =>
    simp only [hf] at h ⊢
    exact inline h
  | some found =>
    simp only [hf] at h ⊢
    by_cases hb : (found == value) = true
    · simp only [hb, ↓reduceIte] at h ⊢
      obtain ⟨hp, hn⟩ := getNat_putNat h
      refine ⟨hp, ?_⟩
      rw [heq _ _ hb] at hf
      simp only [getRef, hn, hf]
    · simp only [hb] at h ⊢
      exact inline h

/-! ### Types and variables -/

theorem getEndian_putEndian {out data : ByteArray} {value : Endian} (h : Prefix (putEndian out value) data) :
    Prefix out data ∧ getEndian data out.size = some (value, (putEndian out value).size) := by
  cases value <;> obtain ⟨hp, hr⟩ := getByte_push h <;> exact ⟨hp, by simp only [getEndian, hr, putEndian]⟩

theorem getTyp_putTyp {out data : ByteArray} {value : Typ} (h : Prefix (putTyp out value) data) :
    Prefix out data ∧ getTyp data out.size = some (value, (putTyp out value).size) := by
  cases value with
  | unknown =>
    obtain ⟨hp, hr⟩ := getByte_push h
    exact ⟨hp, by simp only [getTyp, hr, putTyp]⟩
  | unit =>
    obtain ⟨hp, hr⟩ := getByte_push h
    exact ⟨hp, by simp only [getTyp, hr, putTyp]⟩
  | mem a v =>
    obtain ⟨h2, r2⟩ := getNat_putNat h
    obtain ⟨h1, r1⟩ := getNat_putNat h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getTyp, hr, r1, r2, putTyp, bind, Option.bind]⟩
  | imm w =>
    obtain ⟨h1, r1⟩ := getNat_putNat h
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getTyp, hr, r1, putTyp, bind, Option.bind]⟩

theorem getVar_putVar {out data : ByteArray} {value : Bap.Var} (h : Prefix (putVar out value) data) :
    Prefix out data ∧ getVar data out.size = some (value, (putVar out value).size) := by
  obtain ⟨name, typ, index, isVirtual⟩ := value
  simp only [putVar] at h ⊢
  obtain ⟨h3, r3⟩ := getBool_putBool h
  obtain ⟨h2, r2⟩ := getNat_putNat h3
  obtain ⟨h1, r1⟩ := getTyp_putTyp h2
  obtain ⟨hp, hr⟩ := getText_putText h1
  exact ⟨hp, by simp only [getVar, hr, r1, r2, r3, bind, Option.bind]⟩

theorem beq_var (first second : Bap.Var) (h : (first == second) = true) : first = second := by
  simpa using h

theorem getVarRef {vars : Table Bap.Var} {out data : ByteArray} {value : Bap.Var} (h : Prefix (putVarRef vars out value) data) :
    Prefix out data ∧ getRef (getVar data) vars.items data out.size = some (value, (putVarRef vars out value).size) :=
  getRef_putAt beq_var (fun _ h => getVar_putVar h) h

/-! ### Expressions -/

private theorem binOf_binCode (op : BinOp) : binOf? (binCode op) = some op := by cases op <;> rfl
private theorem unOf_unCode (op : UnOp) : unOf? (unCode op) = some op := by cases op <;> rfl
private theorem castOf_castCode (kind : Cast) : castOf? (castCode kind) = some kind := by cases kind <;> rfl

private theorem shift_value {width : Nat} (value : BitVec width) : value.toNat >>> width = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt value.isLt

theorem getExp_putExp (vars : Table Bap.Var) (data : ByteArray) (value : Exp) :
    ∀ {out : ByteArray} {fuel : Nat}, expDepth value ≤ fuel → Prefix (putExp vars out value) data →
      Prefix out data ∧ getExp vars.items data fuel out.size = some (value, (putExp vars out value).size) := by
  induction value with
  | int bits =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [putExp] at h ⊢
    obtain ⟨h2, r2⟩ := getNat_putNat h
    obtain ⟨h1, r1⟩ := getNat_putNat h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    refine ⟨hp, ?_⟩
    have hv : BitVec.ofNat _ bits.toNat = bits := by simp
    simp only [getExp, hr, r1, r2, bind, Option.bind, shift_value, ↓reduceIte, hv]
  | var var =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [putExp] at h ⊢
    obtain ⟨h1, r1⟩ := getVarRef h
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, bind, Option.bind]⟩
  | load memory address endian size ih1 ih2 =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h4, r4⟩ := getNat_putNat h
    obtain ⟨h3, r3⟩ := getEndian_putEndian h4
    obtain ⟨h2, r2⟩ := ih2 (fuel := f) (by omega) h3
    obtain ⟨h1, r1⟩ := ih1 (fuel := f) (by omega) h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, r4, bind, Option.bind]⟩
  | store memory address value endian size ih1 ih2 ih3 =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h5, r5⟩ := getNat_putNat h
    obtain ⟨h4, r4⟩ := getEndian_putEndian h5
    obtain ⟨h3, r3⟩ := ih3 (fuel := f) (by omega) h4
    obtain ⟨h2, r2⟩ := ih2 (fuel := f) (by omega) h3
    obtain ⟨h1, r1⟩ := ih1 (fuel := f) (by omega) h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, r4, r5, bind, Option.bind]⟩
  | bin op left right ih1 ih2 =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h3, r3⟩ := ih2 (fuel := f) (by omega) h
    obtain ⟨h2, r2⟩ := ih1 (fuel := f) (by omega) h3
    obtain ⟨h1, r1⟩ := getByte_push h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, bind, Option.bind, binOf_binCode]⟩
  | un op value ih =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h2, r2⟩ := ih (fuel := f) (by omega) h
    obtain ⟨h1, r1⟩ := getByte_push h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, bind, Option.bind, unOf_unCode]⟩
  | cast kind width value ih =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h3, r3⟩ := ih (fuel := f) (by omega) h
    obtain ⟨h2, r2⟩ := getNat_putNat h3
    obtain ⟨h1, r1⟩ := getByte_push h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, bind, Option.bind, castOf_castCode]⟩
  | letIn var value body ih1 ih2 =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h3, r3⟩ := ih2 (fuel := f) (by omega) h
    obtain ⟨h2, r2⟩ := ih1 (fuel := f) (by omega) h3
    obtain ⟨h1, r1⟩ := getVarRef h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, bind, Option.bind]⟩
  | ite condition yes no ih1 ih2 ih3 =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h3, r3⟩ := ih3 (fuel := f) (by omega) h
    obtain ⟨h2, r2⟩ := ih2 (fuel := f) (by omega) h3
    obtain ⟨h1, r1⟩ := ih1 (fuel := f) (by omega) h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, bind, Option.bind]⟩
  | extract high low value ih =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h3, r3⟩ := ih (fuel := f) (by omega) h
    obtain ⟨h2, r2⟩ := getNat_putNat h3
    obtain ⟨h1, r1⟩ := getNat_putNat h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, r3, bind, Option.bind]⟩
  | concat left right ih1 ih2 =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [expDepth] at hd
    simp only [putExp] at h ⊢
    obtain ⟨h2, r2⟩ := ih2 (fuel := f) (by omega) h
    obtain ⟨h1, r1⟩ := ih1 (fuel := f) (by omega) h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, bind, Option.bind]⟩
  | unknown message typ =>
    intro out fuel hd h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [expDepth] at hd; omega⟩
    simp only [putExp] at h ⊢
    obtain ⟨h2, r2⟩ := getTyp_putTyp h
    obtain ⟨h1, r1⟩ := getText_putText h2
    obtain ⟨hp, hr⟩ := getByte_push h1
    exact ⟨hp, by simp only [getExp, hr, r1, r2, bind, Option.bind]⟩

/-! ### Statements -/

private theorem stmt_depth_le {stmts : List Stmt} {stmt : Stmt} {fuel : Nat} (hm : stmt ∈ stmts) (hd : stmtsDepth stmts ≤ fuel) :
    stmtDepth stmt ≤ fuel := by
  induction stmts with
  | nil => simp at hm
  | cons head rest ih =>
    simp only [stmtsDepth] at hd
    rcases List.mem_cons.1 hm with rfl | hr
    · omega
    · exact ih hr (by omega)

private theorem putStmts_items (vars : Table Bap.Var) (out : ByteArray) (stmts : List Stmt) :
    putStmts vars out stmts = putItems (putStmt vars) out stmts := by
  induction stmts generalizing out with
  | nil => rfl
  | cons stmt rest ih =>
    rw [putStmts, putItems, ih]

/-- A list of statements is `putList` of them. -/
theorem putStmts_list (vars : Table Bap.Var) (out : ByteArray) (stmts : List Stmt) :
    putStmts vars (putNat out stmts.length) stmts = putList (putStmt vars) out stmts := by
  rw [putStmts_items, putList]

mutual
  theorem getStmt_putStmt (vars : Table Bap.Var) (data : ByteArray) :
      (value : Stmt) → ∀ {out : ByteArray} {fuel : Nat}, stmtDepth value ≤ fuel → Prefix (putStmt vars out value) data →
        Prefix out data ∧ getStmt vars.items data fuel out.size = some (value, (putStmt vars out value).size)
    | .move var value, out, fuel, hd, h => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [stmtDepth] at hd; omega⟩
      simp only [stmtDepth] at hd
      simp only [putStmt] at h ⊢
      obtain ⟨h2, r2⟩ := getExp_putExp vars data value (fuel := f) (by omega) h
      obtain ⟨h1, r1⟩ := getVarRef h2
      obtain ⟨hp, hr⟩ := getByte_push h1
      exact ⟨hp, by rw [getStmt]; simp only [hr, r1, r2, bind, Option.bind]⟩
    | .jmp target, out, fuel, hd, h => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [stmtDepth] at hd; omega⟩
      simp only [stmtDepth] at hd
      simp only [putStmt] at h ⊢
      obtain ⟨h1, r1⟩ := getExp_putExp vars data target (fuel := f) (by omega) h
      obtain ⟨hp, hr⟩ := getByte_push h1
      exact ⟨hp, by rw [getStmt]; simp only [hr, r1, bind, Option.bind]⟩
    | .special message, out, fuel, hd, h => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [stmtDepth] at hd; omega⟩
      simp only [putStmt] at h ⊢
      obtain ⟨h1, r1⟩ := getText_putText h
      obtain ⟨hp, hr⟩ := getByte_push h1
      exact ⟨hp, by rw [getStmt]; simp only [hr, r1, bind, Option.bind]⟩
    | .while condition body, out, fuel, hd, h => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [stmtDepth] at hd; omega⟩
      simp only [stmtDepth] at hd
      simp only [putStmt, putStmts_list] at h ⊢
      obtain ⟨h2, r2⟩ := getStmts_putStmts vars data body (fuel := f) (by omega) h
      obtain ⟨h1, r1⟩ := getExp_putExp vars data condition (fuel := f) (by omega) h2
      obtain ⟨hp, hr⟩ := getByte_push h1
      exact ⟨hp, by rw [getStmt]; simp only [hr, r1, r2, bind, Option.bind]⟩
    | .ifElse condition yes no, out, fuel, hd, h => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [stmtDepth] at hd; omega⟩
      simp only [stmtDepth] at hd
      simp only [putStmt, putStmts_list] at h ⊢
      obtain ⟨h3, r3⟩ := getStmts_putStmts vars data no (fuel := f) (by omega) h
      obtain ⟨h2, r2⟩ := getStmts_putStmts vars data yes (fuel := f) (by omega) h3
      obtain ⟨h1, r1⟩ := getExp_putExp vars data condition (fuel := f) (by omega) h2
      obtain ⟨hp, hr⟩ := getByte_push h1
      exact ⟨hp, by rw [getStmt]; simp only [hr, r1, r2, r3, bind, Option.bind]⟩
    | .cpuExn number, out, fuel, hd, h => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [stmtDepth] at hd; omega⟩
      simp only [putStmt] at h ⊢
      obtain ⟨h1, r1⟩ := getNat_putNat h
      obtain ⟨hp, hr⟩ := getByte_push h1
      exact ⟨hp, by rw [getStmt]; simp only [hr, r1, bind, Option.bind]⟩

  theorem getStmts_putStmts (vars : Table Bap.Var) (data : ByteArray) :
      (stmts : List Stmt) → ∀ {out : ByteArray} {fuel : Nat}, stmtsDepth stmts ≤ fuel → Prefix (putList (putStmt vars) out stmts) data →
        Prefix out data ∧ getList (getStmt vars.items data fuel) data out.size = some (stmts, (putList (putStmt vars) out stmts).size)
    | stmts, out, fuel, hd, h => getList_putList (fun item hm => fun out h => getStmt_putStmt vars data item (stmt_depth_le hm hd) h) h
end

end Bap.Proofs.Binary
