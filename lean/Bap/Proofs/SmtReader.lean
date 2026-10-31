import Bap.Proofs.Symbolic

/-! The reader of the scripts that `renderScript` prints. It is a file of its own so that its proofs aren't paid for by those of
`Bap.Proofs.Symbolic`. There is deliberately no `decide` of `readScript` on a concrete text here: test it in `BapTests`. -/

namespace Bap.Proofs.Symbolic

open Bap.Symbolic

/-! ### Reading the scripts back

`renderScript_wellSorted` says that a script is the printing of a well-sorted tree, but a printer can be right about a tree
while its text means another one: a symbol with a bar in it or a head that runs into its argument. So here is the other
half, a reader of SMT-LIB's concrete syntax: S-expressions of parentheses, whitespace, simple symbols and `|`-quoted
symbols. Reading the text of a well-sorted script recovers the tree. -/

namespace SmtReader

/-- SMT-LIB's S-expressions. An atom keeps its text, the bars of a quoted symbol among it. -/
inductive SExp where
  | atom (text : List Char)
  | list (items : List SExp)

/-- SMT-LIB's whitespace. -/
def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- A character of a simple symbol or a literal. -/
def isPlain (c : Char) : Bool := !(isSpace c || c == '(' || c == ')' || c == '|')

def skipSpace : List Char → List Char
  | [] => []
  | c :: rest => if isSpace c then skipSpace rest else c :: rest

mutual
  /-- The S-expression at the start of the input and what follows it. -/
  def readSExp : Nat → List Char → Option (SExp × List Char)
    | 0, _ => none
    | fuel + 1, input =>
      match skipSpace input with
      | [] => none
      | c :: rest =>
        if c = '(' then
          match readItems fuel rest with
          | some (items, rest) => some (.list items, rest)
          | none => none
        else if c = ')' then none
        else if c = '|' then
          match rest.dropWhile (· != '|') with
          | '|' :: after => some (.atom ('|' :: rest.takeWhile (· != '|') ++ ['|']), after)
          | _ => none
        else
          some (.atom ((c :: rest).takeWhile isPlain), (c :: rest).dropWhile isPlain)

  /-- The S-expressions up to the closing parenthesis, and what follows that. -/
  def readItems : Nat → List Char → Option (List SExp × List Char)
    | 0, _ => none
    | fuel + 1, input =>
      match skipSpace input with
      | ')' :: rest => some ([], rest)
      | input =>
        match readSExp fuel input with
        | none => none
        | some (item, rest) =>
          match readItems fuel rest with
          | none => none
          | some (items, rest) => some (item :: items, rest)
end

/-- All the S-expressions of the input. -/
def readAll : Nat → List Char → Option (List SExp)
  | 0, _ => none
  | fuel + 1, input =>
    match skipSpace input with
    | [] => some []
    | input =>
      match readSExp fuel input with
      | none => none
      | some (item, rest) =>
        match readAll fuel rest with
        | none => none
        | some items => some (item :: items)

mutual
  /-- The text of an S-expression, single spaces apart. -/
  def SExp.chars : SExp → List Char
    | .atom text => text
    | .list items => '(' :: itemsChars items

  /-- The text of S-expressions, single spaces apart, up to and with the closing parenthesis. -/
  def itemsChars : List SExp → List Char
    | [] => [')']
    | [item] => item.chars ++ [')']
    | item :: next :: rest => item.chars ++ ' ' :: itemsChars (next :: rest)
end

/-- A number in decimal. -/
def number (text : List Char) : Option Nat := (String.ofList text).toNat?

/-- `(_ bvN W)`. -/
def numeralTerm : List Char → List Char → Option SmtTerm
  | 'b' :: 'v' :: value, width =>
    match number value, number width with
    | some value, some width => some (.numeral value width)
    | _, _ => none
  | _, _ => none

/-- The term an S-expression is. A head that is a list, like `(_ extract 7 0)`, is the text of the head. -/
def SExp.toTerm : SExp → Option SmtTerm
  | .atom text =>
    some (if text = ['#', 'b', '1'] then .bit true
      else if text = ['#', 'b', '0'] then .bit false
      else .symbol (String.ofList text))
  | .list [.atom ['_'], .atom value, .atom width] => numeralTerm value width
  | .list [head, first] =>
    match first.toTerm with
    | some first => some (.app1 (String.ofList head.chars) first)
    | none => none
  | .list [head, first, second] =>
    match first.toTerm, second.toTerm with
    | some first, some second => some (.app2 (String.ofList head.chars) first second)
    | _, _ => none
  | .list [head, first, second, third] =>
    match first.toTerm, second.toTerm, third.toTerm with
    | some first, some second, some third => some (.app3 (String.ofList head.chars) first second third)
    | _, _, _ => none
  | .list _ => none

/-- The width of `(_ BitVec W)`. -/
def bitVecWidth : SExp → Option Nat
  | .list [.atom ['_'], .atom ['B', 'i', 't', 'V', 'e', 'c'], .atom width] => number width
  | _ => none

/-- The command an S-expression is. -/
def SExp.toCommand : SExp → Option SmtCommand
  | .list [.atom ['s', 'e', 't', '-', 'l', 'o', 'g', 'i', 'c'], .atom logic] => some (.setLogic (String.ofList logic))
  | .list [.atom ['d', 'e', 'c', 'l', 'a', 'r', 'e', '-', 'f', 'u', 'n'], .atom symbol, .list [argument], result] =>
    match bitVecWidth argument, bitVecWidth result with
    | some width, some 8 => some (.declareFun (String.ofList symbol) width)
    | _, _ => none
  | .list [.atom ['d', 'e', 'c', 'l', 'a', 'r', 'e', '-', 'c', 'o', 'n', 's', 't'], .atom symbol, sort] =>
    (bitVecWidth sort).map (.declareConst (String.ofList symbol))
  | .list [.atom ['a', 's', 's', 'e', 'r', 't'], term] => term.toTerm.map .assert
  | .list [.atom ['c', 'h', 'e', 'c', 'k', '-', 's', 'a', 't']] => some .checkSat
  | _ => none

/-- The commands of a script's text. -/
def readScript (text : String) : Option (List SmtCommand) :=
  (readAll (text.toList.length + 2) text.toList).bind fun items => items.mapM SExp.toCommand

/-! Atoms are what the reader takes to be one token. -/

def GoodAtom (text : List Char) : Prop :=
  (text ≠ [] ∧ ∀ c ∈ text, isPlain c = true) ∨ ∃ body, text = '|' :: body ++ ['|'] ∧ '|' ∉ body

mutual
  def SExp.Good : SExp → Prop
    | .atom text => GoodAtom text
    | .list items => itemsGood items

  def itemsGood : List SExp → Prop
    | [] => True
    | item :: rest => item.Good ∧ itemsGood rest
end

/-- What may follow a token without running into it. -/
def Delimited : List Char → Prop
  | [] => True
  | c :: _ => isPlain c = false

private theorem skipSpace_of_not_space {c : Char} (h : isSpace c = false) (rest : List Char) :
    skipSpace (c :: rest) = c :: rest := by
  simp [skipSpace, h]

private theorem plain_not_space {c : Char} (h : isPlain c = true) : isSpace c = false := by
  simp only [isPlain, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  exact h.1.1.1

private theorem plain_ne_open {c : Char} (h : isPlain c = true) : c ≠ '(' := by
  rintro rfl; revert h; decide
private theorem plain_ne_close {c : Char} (h : isPlain c = true) : c ≠ ')' := by
  rintro rfl; revert h; decide
private theorem plain_ne_bar {c : Char} (h : isPlain c = true) : c ≠ '|' := by
  rintro rfl; revert h; decide

private theorem takeWhile_bar (body rest : List Char) (h : '|' ∉ body) :
    (body ++ '|' :: rest).takeWhile (· != '|') = body ∧ (body ++ '|' :: rest).dropWhile (· != '|') = '|' :: rest := by
  have hp : ∀ a ∈ body, (a != '|') = true := fun a ha => by
    have : a ≠ '|' := fun he => h (he ▸ ha)
    simpa using this
  rw [List.takeWhile_append_of_pos hp, List.dropWhile_append_of_pos hp]
  simp

private theorem takeWhile_plain (text rest : List Char) (h : ∀ c ∈ text, isPlain c = true) (hd : Delimited rest) :
    (text ++ rest).takeWhile isPlain = text ∧ (text ++ rest).dropWhile isPlain = rest := by
  rw [List.takeWhile_append_of_pos h, List.dropWhile_append_of_pos h]
  cases rest with
  | nil => simp
  | cons c rest =>
    have : isPlain c = false := hd
    simp [this]

private theorem length_chars_pos : (sx : SExp) → sx.Good → 0 < sx.chars.length
  | .atom text, h => by
    rcases h with ⟨hne, _⟩ | ⟨body, rfl, _⟩
    · exact List.length_pos_iff.mpr hne
    · simp [SExp.chars]
  | .list items, _ => by simp [SExp.chars]

private theorem chars_head : (sx : SExp) → sx.Good → ∃ c tail, sx.chars = c :: tail ∧ isSpace c = false ∧ c ≠ ')'
  | .atom text, h => by
    rcases h with ⟨hne, hplain⟩ | ⟨body, rfl, _⟩
    · cases text with
      | nil => exact absurd rfl hne
      | cons c tail =>
        have hc := hplain c (by simp)
        exact ⟨c, tail, rfl, plain_not_space hc, plain_ne_close hc⟩
    · exact ⟨'|', _, rfl, by decide, by decide⟩
  | .list items, _ => ⟨'(', _, rfl, by decide, by decide⟩

private theorem readItems_item {item : SExp} (h : item.Good) (fuel : Nat) (rest : List Char) :
    readItems (fuel + 1) (item.chars ++ rest) =
      match readSExp fuel (item.chars ++ rest) with
      | none => none
      | some (item, rest) =>
        match readItems fuel rest with
        | none => none
        | some (items, rest) => some (item :: items, rest) := by
  obtain ⟨c, tail, hc, hs, hne⟩ := chars_head item h
  rw [hc, List.cons_append, readItems, skipSpace_of_not_space hs]
  split
  · next heq => cases heq; exact absurd rfl hne
  · rfl

/-- Reading from a space is reading from past it. -/
private theorem skipSpace_cons_space {c : Char} (rest : List Char) (hc : isSpace c = true) :
    skipSpace (c :: rest) = skipSpace rest := by
  simp [skipSpace, hc]

private theorem skipSpace_skipSpace (input : List Char) : skipSpace (skipSpace input) = skipSpace input := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
    by_cases hc : isSpace c = true
    · rw [skipSpace_cons_space _ hc, ih]
    · have hc' : isSpace c = false := by simpa using hc
      rw [skipSpace_of_not_space hc', skipSpace_of_not_space hc']

private theorem readSExp_skip (fuel : Nat) (input : List Char) : readSExp fuel (skipSpace input) = readSExp fuel input := by
  cases fuel with
  | zero => simp [readSExp]
  | succ fuel => rw [readSExp, readSExp, skipSpace_skipSpace]

private theorem readItems_space (fuel : Nat) (rest : List Char) {c : Char} (hc : isSpace c = true) :
    readItems fuel (c :: rest) = readItems fuel rest := by
  cases fuel with
  | zero => simp [readItems]
  | succ fuel =>
    rw [readItems, readItems, skipSpace_cons_space _ hc]

mutual
  /-- Reading the text of an S-expression gives it back. -/
  theorem readSExp_chars : (sx : SExp) → sx.Good → ∀ (fuel : Nat) (rest : List Char), sx.chars.length < fuel →
      Delimited rest → readSExp fuel (sx.chars ++ rest) = some (sx, rest)
    | .atom text, h, fuel, rest, hf, hd => by
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [SExp.chars] at hf; omega⟩
      simp only [SExp.chars]
      rcases h with ⟨hne, hplain⟩ | ⟨body, rfl, hbody⟩
      · cases text with
        | nil => exact absurd rfl hne
        | cons c tail =>
          have hc := hplain c (by simp)
          rw [readSExp, List.cons_append, skipSpace_of_not_space (plain_not_space hc)]
          simp only [plain_ne_open hc, plain_ne_close hc, plain_ne_bar hc, ↓reduceIte]
          obtain ⟨h1, h2⟩ := takeWhile_plain (c :: tail) rest hplain hd
          simp only [List.cons_append] at h1 h2
          rw [h1, h2]
      · rw [readSExp]
        have hsk : skipSpace (('|' :: body ++ ['|']) ++ rest) = '|' :: (body ++ '|' :: rest) := by
          simp only [List.cons_append, List.append_assoc, List.nil_append]
          exact skipSpace_of_not_space (by decide) _
        rw [hsk]
        obtain ⟨h1, h2⟩ := takeWhile_bar body rest hbody
        simp [h1, h2]
    | .list items, h, fuel, rest, hf, _ => by
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [SExp.chars] at hf; omega⟩
      simp only [SExp.chars, List.length_cons] at hf ⊢
      rw [readSExp, List.cons_append, skipSpace_of_not_space (by decide)]
      simp only [↓reduceIte]
      rw [readItems_chars items h fuel rest (by omega)]

  /-- Reading the text of S-expressions up to their closing parenthesis gives them back. -/
  theorem readItems_chars : (items : List SExp) → itemsGood items → ∀ (fuel : Nat) (rest : List Char),
      (itemsChars items).length < fuel → readItems fuel (itemsChars items ++ rest) = some (items, rest)
    | [], _, fuel, rest, hf => by
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp only [itemsChars, List.length_cons] at hf; omega⟩
      rw [readItems, show itemsChars [] ++ rest = ')' :: rest from rfl, skipSpace_of_not_space (by decide)]
      rfl
    | [item], ⟨hi, _⟩, fuel, rest, hf => by
      simp only [itemsChars, List.length_append, List.length_cons, List.length_nil] at hf
      have hpos := length_chars_pos item hi
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [itemsChars, List.append_assoc, List.cons_append, List.nil_append]
      rw [readItems_item hi, readSExp_chars item hi fuel _ (by omega) (show Delimited (_ :: _) by show isPlain _ = false; decide)]
      simp only
      rw [show ')' :: rest = itemsChars [] ++ rest from rfl, readItems_chars [] trivial fuel rest (by
        simp only [itemsChars, List.length_cons, List.length_nil]; omega)]
    | item :: next :: tail, ⟨hi, hn⟩, fuel, rest, hf => by
      simp only [itemsChars, List.length_append, List.length_cons] at hf
      have hpos := length_chars_pos item hi
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [itemsChars, List.append_assoc, List.cons_append]
      rw [readItems_item hi, readSExp_chars item hi fuel _ (by omega) (show Delimited (_ :: _) by show isPlain _ = false; decide)]
      simp only
      have hskip : readItems fuel (' ' :: (itemsChars (next :: tail) ++ rest)) =
          readItems fuel (itemsChars (next :: tail) ++ rest) := readItems_space _ _ (by decide)
      rw [hskip, readItems_chars (next :: tail) hn fuel rest (by omega)]
end

/-! The terms and commands of a well-sorted script are the S-expressions they print as. -/

/-- A term is what the text of an S-expression says, and so what reading the text gets. -/
def Repr (t : SmtTerm) (sx : SExp) : Prop := sx.chars = t.print.toList ∧ sx.Good ∧ sx.toTerm = some t

private theorem goodAtom_of_valid {symbol : String} (h : ValidSymbol symbol) : GoodAtom symbol.toList := by
  obtain ⟨body, hb, hbar, _⟩ := h
  exact .inr ⟨body, by simpa using hb, hbar⟩

private theorem goodAtom_literal {text : List Char} (h : text ≠ [] ∧ text.all isPlain = true) : GoodAtom text :=
  .inl ⟨h.1, List.all_eq_true.mp h.2⟩

private theorem isPlain_digit {c : Char} (h : c.isDigit = true) : isPlain c = true := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
  have hd1 : ('0' : Char).val.toNat = 48 := rfl
  have hd2 : ('9' : Char).val.toNat = 57 := rfl
  rw [hd1, hd2] at h
  simp only [isPlain, isSpace, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> (rintro rfl; revert h; decide)

private theorem digits_plain (n : Nat) : ∀ c ∈ (toString n).toList, isPlain c = true := by
  intro c hc
  apply isPlain_digit
  rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

private theorem digits_ne (n : Nat) : (toString n).toList ≠ [] := by
  rw [Nat.toString_eq_repr, Nat.toList_repr]
  simp [Nat.toDigits_ne_nil]

private theorem goodAtom_digits (n : Nat) : GoodAtom (toString n).toList := .inl ⟨digits_ne n, digits_plain n⟩

private theorem number_digits (n : Nat) : number (toString n).toList = some n := by
  simp only [number, String.ofList_toList, Nat.toString_eq_repr]
  exact Nat.toNat?_repr n

private theorem Repr.symbol {name : String} (h : ValidSymbol name) : Repr (.symbol name) (.atom name.toList) := by
  refine ⟨rfl, goodAtom_of_valid h, ?_⟩
  obtain ⟨body, hb, _⟩ := h
  have h1 : name.toList ≠ ['#', 'b', '1'] := by simp [hb]
  have h2 : name.toList ≠ ['#', 'b', '0'] := by simp [hb]
  simp only [SExp.toTerm, h1, h2, ↓reduceIte, String.ofList_toList]

private theorem Repr.numeral (value width : Nat) :
    Repr (.numeral value width)
      (.list [.atom ['_'], .atom ('b' :: 'v' :: (toString value).toList), .atom (toString width).toList]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [SExp.chars, itemsChars, SmtTerm.print, String.toList_append, toString]
  · refine ⟨.inl ⟨by simp, by decide⟩, .inl ⟨by simp, ?_⟩, goodAtom_digits width, trivial⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · decide
    · decide
    · exact digits_plain value c hc
  · have h1 := number_digits value
    have h2 := number_digits width
    simp only [Nat.toString_eq_repr, Nat.toList_repr] at h1 h2
    simp [SExp.toTerm, numeralTerm, h1, h2]

private theorem Repr.bit (value : Bool) :
    Repr (.bit value) (.atom (if value then ['#', 'b', '1'] else ['#', 'b', '0'])) := by
  refine ⟨?_, ?_, ?_⟩
  · cases value <;> rfl
  · cases value
    · exact goodAtom_literal (by decide)
    · exact goodAtom_literal (by decide)
  · cases value <;> simp [SExp.toTerm]

private theorem Repr.app1 {head : String} {headSx sx : SExp} {t : SmtTerm} (hh : headSx.chars = head.toList)
    (hg : headSx.Good) (h : Repr t sx) : Repr (.app1 head t) (.list [headSx, sx]) := by
  obtain ⟨hc, hgood, ht⟩ := h
  refine ⟨?_, ⟨hg, hgood, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtTerm.print, String.toList_append, toString, hh, hc]
  · simp [SExp.toTerm, ht, hh]

private theorem Repr.app2 {head : String} {sx₁ sx₂ : SExp} {t₁ t₂ : SmtTerm} {headSx : SExp}
    (hh : headSx.chars = head.toList) (hg : headSx.Good) (hne : headSx.chars ≠ ['_']) (h₁ : Repr t₁ sx₁) (h₂ : Repr t₂ sx₂) :
    Repr (.app2 head t₁ t₂) (.list [headSx, sx₁, sx₂]) := by
  obtain ⟨hc₁, hgood₁, ht₁⟩ := h₁
  obtain ⟨hc₂, hgood₂, ht₂⟩ := h₂
  refine ⟨?_, ⟨hg, hgood₁, hgood₂, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtTerm.print, String.toList_append, toString, hh, hc₁, hc₂]
  · rw [SExp.toTerm.eq_4 _ _ _ (fun _ _ he _ _ => hne (by rw [he]; rfl)), ht₁, ht₂, hh, String.ofList_toList]

private theorem Repr.app3 {head : String} {sx₁ sx₂ sx₃ : SExp} {t₁ t₂ t₃ : SmtTerm} {headSx : SExp}
    (hh : headSx.chars = head.toList) (hg : headSx.Good) (h₁ : Repr t₁ sx₁) (h₂ : Repr t₂ sx₂) (h₃ : Repr t₃ sx₃) :
    Repr (.app3 head t₁ t₂ t₃) (.list [headSx, sx₁, sx₂, sx₃]) := by
  obtain ⟨hc₁, hgood₁, ht₁⟩ := h₁
  obtain ⟨hc₂, hgood₂, ht₂⟩ := h₂
  obtain ⟨hc₃, hgood₃, ht₃⟩ := h₃
  refine ⟨?_, ⟨hg, hgood₁, hgood₂, hgood₃, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtTerm.print, String.toList_append, toString, hh, hc₁, hc₂, hc₃]
  · simp [SExp.toTerm, ht₁, ht₂, ht₃, hh]

/-- The symbols of a signature are valid. -/
def SigValid (Γ : SmtSignature) : Prop :=
  (∀ x ∈ Γ.constants, ValidSymbol x.1) ∧ ∀ x ∈ Γ.functions, ValidSymbol x.1

private theorem atom_head {name : String} (h : name.toList ≠ [] ∧ name.toList.all isPlain = true) :
    (SExp.atom name.toList).chars = name.toList ∧ (SExp.atom name.toList).Good := ⟨rfl, goodAtom_literal h⟩

private theorem atom_valid {name : String} (h : ValidSymbol name) :
    (SExp.atom name.toList).chars = name.toList ∧ (SExp.atom name.toList).Good ∧ (SExp.atom name.toList).chars ≠ ['_'] := by
  refine ⟨rfl, goodAtom_of_valid h, ?_⟩
  obtain ⟨body, hb, _⟩ := h
  simp only [SExp.chars, hb]
  simp

/-- Every well-sorted term has an S-expression, and that is what its text reads as. -/
theorem HasSort.repr {Γ : SmtSignature} (hΓ : SigValid Γ) {t : SmtTerm} {sort : SmtSort} (h : HasSort Γ t sort) :
    ∃ sx, Repr t sx := by
  induction h with
  | constant hm => exact ⟨_, Repr.symbol (hΓ.1 _ hm)⟩
  | numeral _ _ => exact ⟨_, Repr.numeral _ _⟩
  | bit value => exact ⟨_, Repr.bit value⟩
  | function hm _ ih =>
    obtain ⟨sx, hsx⟩ := ih
    obtain ⟨h1, h2, _⟩ := atom_valid (hΓ.2 _ hm)
    exact ⟨_, Repr.app1 h1 h2 hsx⟩
  | arithmetic hname _ _ ihl ihr =>
    obtain ⟨sl, hl⟩ := ihl
    obtain ⟨sr, hr⟩ := ihr
    simp only [bvArithmetic, List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, Repr.app2 (headSx := .atom _) rfl (goodAtom_literal (by decide)) (by decide) hl hr⟩
  | comparison hname _ _ ihl ihr =>
    obtain ⟨sl, hl⟩ := ihl
    obtain ⟨sr, hr⟩ := ihr
    simp only [bvComparison, List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, Repr.app2 (headSx := .atom _) rfl (goodAtom_literal (by decide)) (by decide) hl hr⟩
  | equal hname _ _ ihl ihr =>
    obtain ⟨sl, hl⟩ := ihl
    obtain ⟨sr, hr⟩ := ihr
    rcases hname with rfl | rfl <;>
      exact ⟨_, Repr.app2 (headSx := .atom _) rfl (goodAtom_literal (by decide)) (by decide) hl hr⟩
  | unary hname _ ih =>
    obtain ⟨sx, hsx⟩ := ih
    rcases hname with rfl | rfl <;>
      exact ⟨_, Repr.app1 (headSx := .atom _) rfl (goodAtom_literal (by decide)) hsx⟩
  | @extension kind extra _ _ hkind _ ih =>
    obtain ⟨sx, hsx⟩ := ih
    refine ⟨.list [.list [.atom ['_'], .atom kind.toList, .atom (toString extra).toList], sx], Repr.app1 ?_ ?_ hsx⟩
    · simp [SExp.chars, itemsChars, String.toList_append, toString]
    · refine ⟨.inl ⟨by simp, by decide⟩, ?_, goodAtom_digits extra, trivial⟩
      rcases hkind with rfl | rfl <;> exact goodAtom_literal (by decide)
  | @extract high low _ _ _ _ _ ih =>
    obtain ⟨sx, hsx⟩ := ih
    refine ⟨.list [.list [.atom ['_'], .atom "extract".toList, .atom (toString high).toList,
      .atom (toString low).toList], sx], Repr.app1 ?_ ?_ hsx⟩
    · simp [SExp.chars, itemsChars, String.toList_append, toString]
    · exact ⟨.inl ⟨by simp, by decide⟩, goodAtom_literal (by decide), goodAtom_digits high, goodAtom_digits low, trivial⟩
  | concat _ _ ihl ihr =>
    obtain ⟨sl, hl⟩ := ihl
    obtain ⟨sr, hr⟩ := ihr
    exact ⟨_, Repr.app2 (headSx := .atom _) rfl (goodAtom_literal (by decide)) (by decide) hl hr⟩
  | ite _ _ _ ihc ihy ihn =>
    obtain ⟨sc, hc⟩ := ihc
    obtain ⟨sy, hy⟩ := ihy
    obtain ⟨sn, hn⟩ := ihn
    exact ⟨_, Repr.app3 (headSx := .atom _) rfl (goodAtom_literal (by decide)) hc hy hn⟩

/-- A command is what the text of an S-expression says. -/
def CommandRepr (command : SmtCommand) : Prop :=
  ∃ sx : SExp, sx.chars = command.print.toList ∧ sx.Good ∧ sx.toCommand = some command

private theorem bitVec_repr (width : Nat) :
    let sort := SExp.list [.atom ['_'], .atom ['B', 'i', 't', 'V', 'e', 'c'], .atom (toString width).toList]
    sort.Good ∧ bitVecWidth sort = some width := by
  refine ⟨⟨.inl ⟨by simp, by decide⟩, goodAtom_literal (by decide), goodAtom_digits width, trivial⟩, ?_⟩
  simp only [bitVecWidth]
  exact number_digits width

private theorem CommandRepr.assert {Γ : SmtSignature} (hΓ : SigValid Γ) {term : SmtTerm} (h : HasSort Γ term .bool) :
    CommandRepr (.assert term) := by
  obtain ⟨sx, hc, hg, ht⟩ := HasSort.repr hΓ h
  refine ⟨.list [.atom ['a', 's', 's', 'e', 'r', 't'], sx], ?_, ⟨goodAtom_literal (by decide), hg, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtCommand.print, String.toList_append, toString, hc]
  · simp [SExp.toCommand, ht]

private theorem CommandRepr.checkSat : CommandRepr .checkSat :=
  ⟨.list [.atom ['c', 'h', 'e', 'c', 'k', '-', 's', 'a', 't']], rfl, ⟨goodAtom_literal (by decide), trivial⟩, rfl⟩

private theorem CommandRepr.declareConst {symbol : String} {width : Nat} (h : ValidSymbol symbol) :
    CommandRepr (.declareConst symbol width) := by
  obtain ⟨hg, hw⟩ := bitVec_repr width
  refine ⟨.list [.atom ['d', 'e', 'c', 'l', 'a', 'r', 'e', '-', 'c', 'o', 'n', 's', 't'], .atom symbol.toList, _], ?_,
    ⟨goodAtom_literal (by decide), goodAtom_of_valid h, hg, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtCommand.print, String.toList_append, toString]
  · simp only [SExp.toCommand, hw, Option.map_some, String.ofList_toList]

private theorem CommandRepr.declareFun {symbol : String} {width : Nat} (h : ValidSymbol symbol) :
    CommandRepr (.declareFun symbol width) := by
  obtain ⟨hg, hw⟩ := bitVec_repr width
  obtain ⟨hg8, hw8⟩ := bitVec_repr 8
  refine ⟨.list [.atom ['d', 'e', 'c', 'l', 'a', 'r', 'e', '-', 'f', 'u', 'n'], .atom symbol.toList, .list [_], _], ?_,
    ⟨goodAtom_literal (by decide), goodAtom_of_valid h, ⟨hg, trivial⟩, hg8, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtCommand.print, String.toList_append, toString, show Nat.toDigits 10 8 = ['8'] from rfl]
  · simp only [SExp.toCommand, hw, hw8, String.ofList_toList]

private theorem CommandRepr.setLogic {logic : String} (h : logic = "QF_UFBV" ∨ logic = "QF_BV") :
    CommandRepr (.setLogic logic) := by
  refine ⟨.list [.atom ['s', 'e', 't', '-', 'l', 'o', 'g', 'i', 'c'], .atom logic.toList], ?_,
    ⟨goodAtom_literal (by decide), ?_, trivial⟩, ?_⟩
  · simp [SExp.chars, itemsChars, SmtCommand.print, String.toList_append, toString]
  · rcases h with rfl | rfl <;> exact goodAtom_literal (by decide)
  · simp [SExp.toCommand]

/-- Every command of a well-sorted script has an S-expression. -/
theorem ScriptSorted.repr {Γ : SmtSignature} {script : List SmtCommand} (hΓ : SigValid Γ) (h : ScriptSorted Γ script) :
    ∀ command ∈ script, CommandRepr command := by
  induction h with
  | nil => simp
  | checkSat _ ih =>
    intro command hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact CommandRepr.checkSat
    · exact ih hΓ _ hm
  | assert ht _ ih =>
    intro command hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact CommandRepr.assert hΓ ht
    · exact ih hΓ _ hm
  | declareFun _ hv _ _ ih =>
    intro command hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact CommandRepr.declareFun hv
    · refine ih ⟨hΓ.1, fun x hx => ?_⟩ _ hm
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv
      · exact hΓ.2 _ hx
  | declareConst _ hv _ _ ih =>
    intro command hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact CommandRepr.declareConst hv
    · refine ih ⟨fun x hx => ?_, hΓ.2⟩ _ hm
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv
      · exact hΓ.1 _ hx

private theorem readAll_space (fuel : Nat) (rest : List Char) {c : Char} (hc : isSpace c = true) :
    readAll fuel (c :: rest) = readAll fuel rest := by
  cases fuel with
  | zero => simp [readAll]
  | succ fuel => rw [readAll, readAll, skipSpace_cons_space _ hc]

private theorem readAll_item {item : SExp} (h : item.Good) (fuel : Nat) (rest : List Char) :
    readAll (fuel + 1) (item.chars ++ rest) =
      match readSExp fuel (item.chars ++ rest) with
      | none => none
      | some (item, rest) =>
        match readAll fuel rest with
        | none => none
        | some items => some (item :: items) := by
  obtain ⟨c, tail, hc, hs, _⟩ := chars_head item h
  rw [hc, List.cons_append, readAll, skipSpace_of_not_space hs]

private theorem readAll_nil {fuel : Nat} (h : 0 < fuel) : readAll fuel [] = some [] := by
  obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rfl

/-- The text of commands, a line each, reads as those commands. -/
theorem readAll_lines : (commands : List SmtCommand) → (∀ command ∈ commands, CommandRepr command) → ∀ fuel,
    (String.intercalate "\n" (commands.map SmtCommand.print)).toList.length + 1 < fuel →
    (readAll fuel (String.intercalate "\n" (commands.map SmtCommand.print)).toList).bind
      (fun items => items.mapM SExp.toCommand) = some commands
  | [], _, fuel, hf => by
    simp only [List.map_nil]
    rw [show (String.intercalate "\n" []).toList = [] from rfl, readAll_nil (by omega)]
    rfl
  | [command], h, fuel, hf => by
    obtain ⟨sx, hc, hg, ht⟩ := h command (by simp)
    simp only [List.map_cons, List.map_nil, String.intercalate_singleton] at hf ⊢
    rw [← hc] at hf ⊢
    have hpos := length_chars_pos sx hg
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hread := readAll_item hg fuel []
    rw [readSExp_chars sx hg fuel [] (by omega) trivial, List.append_nil] at hread
    simp only [readAll_nil (show 0 < fuel by omega)] at hread
    rw [hread]
    simp [List.mapM_cons, ht]
  | command :: next :: rest, h, fuel, hf => by
    obtain ⟨sx, hc, hg, ht⟩ := h command (by simp)
    have htext : (String.intercalate "\n" ((command :: next :: rest).map SmtCommand.print)).toList =
        sx.chars ++ '\n' :: (String.intercalate "\n" ((next :: rest).map SmtCommand.print)).toList := by
      simp only [List.map_cons, String.intercalate_cons_cons, String.toList_append, hc, List.append_assoc]
      rfl
    rw [htext] at hf ⊢
    simp only [List.length_append, List.length_cons] at hf
    have hpos := length_chars_pos sx hg
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [readAll_item hg fuel, readSExp_chars sx hg fuel _ (by omega) (show Delimited (_ :: _) by show isPlain _ = false; decide)]
    simp only
    rw [readAll_space fuel _ (by decide)]
    have ih := readAll_lines (next :: rest) (fun c hm => h c (List.mem_cons_of_mem _ hm)) fuel (by omega)
    cases hall : readAll fuel (String.intercalate "\n" ((next :: rest).map SmtCommand.print)).toList with
    | none =>
      rw [hall] at ih
      cases ih
    | some items =>
      rw [hall, Option.bind_some] at ih
      simp [List.mapM_cons, ht, ih]

/-- **Reading the text of a well-sorted script recovers the script.** -/
theorem readScript_print {script : List SmtCommand} (h : WellSortedScript script) :
    readScript (String.intercalate "\n" (script.map SmtCommand.print)) = some script := by
  match script, h with
  | .setLogic logic :: rest, ⟨hsorted, hlogic⟩ =>
    apply readAll_lines _ _ _ (by omega)
    intro command hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact CommandRepr.setLogic (hlogic.imp id And.left)
    · exact ScriptSorted.repr (Γ := {}) ⟨by simp, by simp⟩ hsorted _ hm

end SmtReader

/-- **What `renderScript` returns reads as a well-sorted script**: the text Z3 is given is the printing of a tree, which a
reader of SMT-LIB's syntax gets back, and well-sortedness is about that tree. -/
theorem renderScript_reads {constraints : List Expr} (h : ∀ c ∈ constraints, WellSorted c) :
    ∃ script : List SmtCommand, SmtReader.readScript (renderScript constraints) = some script ∧ WellSortedScript script := by
  obtain ⟨script, hprint, hsorted⟩ := renderScript_wellSorted h
  exact ⟨script, by rw [← hprint]; exact SmtReader.readScript_print hsorted, hsorted⟩


end Bap.Proofs.Symbolic
