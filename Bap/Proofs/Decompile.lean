import Lean.Elab.Command
import Bap.Decompile.Project

namespace Bap.Proofs.Decompile

open Lean Elab Command in
/-- `open_private Mod in Ns : a b` names private declarations `Ns.a`, `Ns.b` of module `Mod`
as `a`, `b` for the rest of the current scope. -/
local elab "open_private " mod:ident " in " ns:ident " : " names:ident* : command => do
  for name in names do
    let target := (Name.mkNum (`_private ++ mod.getId) 0) ++ (ns.getId ++ name.getId)
    unless (← getEnv).contains target do
      throwErrorAt name "no private declaration {target}"
    modifyScope fun scope =>
      { scope with openDecls := .explicit name.getId target :: scope.openDecls }

/-- Induction for the nested `Stmt` type, with a hypothesis for every statement of a child block. -/
theorem stmtInduction {P : Bap.Bil.Stmt → Prop}
    (move : ∀ var value, P (.move var value))
    (jmp : ∀ target, P (.jmp target))
    (special : ∀ message, P (.special message))
    (cpuExn : ∀ number, P (.cpuExn number))
    (while_ : ∀ condition body, (∀ s ∈ body, P s) → P (.while condition body))
    (ifElse : ∀ condition yes no, (∀ s ∈ yes, P s) → (∀ s ∈ no, P s) → P (.ifElse condition yes no))
    (stmt : Bap.Bil.Stmt) : P stmt :=
  Bap.Bil.Stmt.rec (motive_1 := P) (motive_2 := fun code => ∀ s ∈ code, P s)
    move jmp special while_ ifElse cpuExn
    (by simp) (by
      intro head tail hh ht s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hh
      · exact ht s hs) stmt

open Bap.Bil (Exp Stmt BinOp)
open Bap.Decompile (exp stmt program function project expIn stmtIn)

open_private Bap.Decompile in Bap.Decompile : hex identifier varName quote endianName binName withWidth leftOperand leftNeedsWidth
  signedBinName unName castName indentation ctype escape escapeChars keywords typeCode expVars stmtVars
open_private Bap.Decompile.Project in Bap.Decompile : usedStmt usedInsns functionDisasm
open_private Bap.Analysis.Xrefs in Bap.Analysis.Xrefs : spans nearestStart
open_private Bap.Core.Sexp in Bap.Sexp : needsQuotes
open_private Bap.Core.Sexp in Bap : Sexp.escape

/-! ### Identifiers and indentation -/

private def hexChars : List Char := "0123456789abcdef".toList

private theorem toDigits16_step (n : Nat) (h : ¬ n < 16) :
    Nat.toDigits 16 n = Nat.toDigits 16 (n / 16) ++ [(n % 16).digitChar] := by
  rw [Nat.toDigits_eq_ite (by decide)]; simp [h]

private theorem digitChar_hex : ∀ d, d < 16 → d.digitChar ∈ hexChars := by decide

private theorem toDigits16_hex (n : Nat) : ∀ c ∈ Nat.toDigits 16 n, c ∈ hexChars := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 16
    · rw [Nat.toDigits_of_lt_base h]
      simpa using digitChar_hex n h
    · rw [toDigits16_step n h]
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih _ (by omega) c hc
      · simp at hc; subst hc; exact digitChar_hex _ (Nat.mod_lt _ (by decide))

private def hexValue (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

private theorem hexValue_digitChar : ∀ d, d < 16 → hexValue d.digitChar = d := by decide

private def hexStep (acc : Nat) (c : Char) : Nat := acc * 16 + hexValue c

private theorem foldl_toDigits16 (n : Nat) : (Nat.toDigits 16 n).foldl hexStep 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 16
    · rw [Nat.toDigits_of_lt_base h]
      simp [hexStep, hexValue_digitChar n h]
    · rw [toDigits16_step n h, List.foldl_append, ih _ (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, hexStep]
      rw [hexValue_digitChar _ (Nat.mod_lt _ (by decide))]
      omega

private def parseHex : Nat → List Char → Nat × List Char
  | acc, [] => (acc, [])
  | acc, c :: rest => if c = '_' then (acc, rest) else parseHex (hexStep acc c) rest

private theorem parseHex_digits (ds rest : List Char) (acc : Nat) (h : ∀ c ∈ ds, c ≠ '_') :
    parseHex acc (ds ++ '_' :: rest) = (ds.foldl hexStep acc, rest) := by
  induction ds generalizing acc with
  | nil => simp [parseHex]
  | cons c ds ih =>
    simp only [List.cons_append, parseHex, List.foldl_cons]
    simp only [h c (by simp), ↓reduceIte]
    exact ih _ fun d hd => h d (by simp [hd])

/-- Inverse of the identifier encoding: the decoded name, and the rest from the first `_0v` or
`_0t` marker on. -/
private def decode : Nat → List Char → List Char × List Char
  | 0, _ => ([], [])
  | _ + 1, [] => ([], [])
  | fuel + 1, c :: rest =>
    if c = '_' ∧ rest.take 2 = ['0', 'x'] then
      if (rest.drop 2).head? = some '_' then decode fuel (rest.drop 3)
      else
        let parsed := parseHex 0 (rest.drop 2)
        let tail := decode fuel parsed.2
        (Char.ofNat parsed.1 :: tail.1, tail.2)
    else if c = '_' ∧ (rest.take 2 = ['0', 'v'] ∨ rest.take 2 = ['0', 't']) then ([], c :: rest)
    else
      let tail := decode fuel rest
      (c :: tail.1, tail.2)

private theorem hex_ne_underscore {c : Char} (h : c ∈ hexChars) : c ≠ '_' := by
  have : ∀ d ∈ hexChars, d ≠ '_' := by decide
  exact this c h

private theorem decode_escape (c : Char) (rest : List Char) (fuel : Nat) :
    decode (fuel + 1) (escape c ++ rest) =
      (c :: (decode fuel rest).1, (decode fuel rest).2) := by
  have hd : ∀ d ∈ Nat.toDigits 16 c.toNat, d ≠ '_' := fun d hd =>
    hex_ne_underscore (toDigits16_hex _ d hd)
  obtain ⟨head, tail, hdigits⟩ : ∃ head tail, Nat.toDigits 16 c.toNat = head :: tail :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hhead : head ≠ '_' := hd head (by simp [hdigits])
  have hp := parseHex_digits (Nat.toDigits 16 c.toNat) rest 0 hd
  rw [foldl_toDigits16] at hp
  simp only [escape, List.cons_append, List.append_assoc]
  rw [decode]
  simp only [List.nil_append]
  rw [hdigits] at hp ⊢
  simp only [List.cons_append] at hp
  simp [hhead, hp, Char.ofNat_toNat]

private theorem escapeChars_x (rest : List Char) :
    escapeChars ('_' :: '0' :: 'x' :: rest) = escape '_' ++ '0' :: 'x' :: escapeChars rest := by
  rw [escapeChars]

private theorem escapeChars_v (rest : List Char) :
    escapeChars ('_' :: '0' :: 'v' :: rest) = escape '_' ++ '0' :: 'v' :: escapeChars rest := by
  rw [escapeChars]

private theorem escapeChars_t (rest : List Char) :
    escapeChars ('_' :: '0' :: 't' :: rest) = escape '_' ++ '0' :: 't' :: escapeChars rest := by
  rw [escapeChars]

private theorem escapeChars_other {c : Char} {rest : List Char}
    (hx : ∀ r, c = '_' → rest = '0' :: 'x' :: r → False)
    (hv : ∀ r, c = '_' → rest = '0' :: 'v' :: r → False)
    (ht : ∀ r, c = '_' → rest = '0' :: 't' :: r → False) :
    escapeChars (c :: rest) =
      if c.isAlphanum || c = '_' then c :: escapeChars rest else escape c ++ escapeChars rest := by
  rw [escapeChars]
  · exact fun r h1 h2 => hx r (by simpa using h1) (by simpa using h2)
  · exact fun r h1 h2 => hv r (by simpa using h1) (by simpa using h2)
  · exact fun r h1 h2 => ht r (by simpa using h1) (by simpa using h2)

private theorem escapeChars_induct {P : List Char → Prop} (nil : P [])
    (x : ∀ r, P r → P ('_' :: '0' :: 'x' :: r)) (v : ∀ r, P r → P ('_' :: '0' :: 'v' :: r))
    (t : ∀ r, P r → P ('_' :: '0' :: 't' :: r))
    (other : ∀ c rest, (∀ r, c = '_' → rest = '0' :: 'x' :: r → False) →
      (∀ r, c = '_' → rest = '0' :: 'v' :: r → False) →
      (∀ r, c = '_' → rest = '0' :: 't' :: r → False) → P rest → P (c :: rest))
    (cs : List Char) : P cs := by
  generalize hn : cs.length = n
  induction n using Nat.strongRecOn generalizing cs with
  | _ n ih =>
    cases cs with
    | nil => exact nil
    | cons c rest =>
      simp only [List.length_cons] at hn
      by_cases hx : ∃ r, c = '_' ∧ rest = '0' :: 'x' :: r
      · obtain ⟨r, rfl, rfl⟩ := hx
        exact x r (ih _ (by simp at hn; omega) r rfl)
      · by_cases hv : ∃ r, c = '_' ∧ rest = '0' :: 'v' :: r
        · obtain ⟨r, rfl, rfl⟩ := hv
          exact v r (ih _ (by simp at hn; omega) r rfl)
        · by_cases ht : ∃ r, c = '_' ∧ rest = '0' :: 't' :: r
          · obtain ⟨r, rfl, rfl⟩ := ht
            exact t r (ih _ (by simp at hn; omega) r rfl)
          · exact other c rest (fun r a b => hx ⟨r, a, b⟩) (fun r a b => hv ⟨r, a, b⟩)
              (fun r a b => ht ⟨r, a, b⟩) (ih _ (by omega) rest rfl)

private theorem escapeChars_zero (r : List Char) : escapeChars ('0' :: r) = '0' :: escapeChars r := by
  rw [escapeChars_other (by simp) (by simp) (by simp)]
  simp

private theorem escape_head (c : Char) (suffix : List Char) :
    (escape c ++ suffix).head? = some '_' := by
  simp [escape]

/-- The first rendered character is `_` or the first source character. -/
private theorem head_escapeChars (r suffix : List Char) (hs : ∀ c, suffix.head? = some c → c = '_')
    (c : Char) (h : (escapeChars r ++ suffix).head? = some c) : c = '_' ∨ r.head? = some c := by
  induction r using escapeChars_induct with
  | nil => exact Or.inl (hs c (by simpa [escapeChars] using h))
  | x r _ =>
    rw [escapeChars_x, List.append_assoc, escape_head] at h
    exact Or.inl (Option.some.inj h).symm
  | v r _ =>
    rw [escapeChars_v, List.append_assoc, escape_head] at h
    exact Or.inl (Option.some.inj h).symm
  | t r _ =>
    rw [escapeChars_t, List.append_assoc, escape_head] at h
    exact Or.inl (Option.some.inj h).symm
  | other d rest hx hv ht _ =>
    rw [escapeChars_other hx hv ht] at h
    split at h
    · right; simpa using h
    · rw [List.append_assoc, escape_head] at h
      exact Or.inl (Option.some.inj h).symm

private theorem length_escape_pos (c : Char) (rest : List Char) :
    rest.length + 1 ≤ (escape c ++ rest).length := by
  simp [escape]; omega

private theorem decode_literals (m : Char) (rest : List Char) (fuel : Nat) :
    decode (fuel + 2) ('0' :: m :: rest) =
      ('0' :: (decode (fuel + 1) (m :: rest)).1, (decode (fuel + 1) (m :: rest)).2) := by
  rw [decode]
  simp

/-- A literal `_` is not read as a marker unless the source text had one. -/
private theorem no_marker {rest suffix : List Char} (hs : ∀ c, suffix.head? = some c → c = '_')
    (hx : ∀ r, rest = '0' :: 'x' :: r → False) (hv : ∀ r, rest = '0' :: 'v' :: r → False)
    (ht : ∀ r, rest = '0' :: 't' :: r → False)
    (m : Char) (hm : m = 'x' ∨ m = 'v' ∨ m = 't') : (escapeChars rest ++ suffix).take 2 ≠ ['0', m] := by
  intro htake
  cases hl : escapeChars rest ++ suffix with
  | nil => simp [hl] at htake
  | cons a l =>
    cases l with
    | nil => simp [hl] at htake
    | cons b l =>
      simp [hl] at htake
      obtain ⟨rfl, rfl⟩ := htake
      have h0 := head_escapeChars rest suffix hs '0' (by simp [hl])
      simp at h0
      cases rest with
      | nil => simp at h0
      | cons a' r =>
        simp at h0
        subst h0
        rw [escapeChars_zero] at hl
        simp at hl
        have hm' := head_escapeChars r suffix hs b (by simp [hl])
        rcases hm with rfl | rfl | rfl
        · simp at hm'
          cases r with
          | nil => simp at hm'
          | cons a'' r => simp at hm'; subst hm'; exact hx r rfl
        · simp at hm'
          cases r with
          | nil => simp at hm'
          | cons a'' r => simp at hm'; subst hm'; exact hv r rfl
        · simp at hm'
          cases r with
          | nil => simp at hm'
          | cons a'' r => simp at hm'; subst hm'; exact ht r rfl

/-- `decode` undoes `escapeChars`, up to a tail which starts with `_` or is empty. -/
private theorem decode_escapeChars (cs suffix tail : List Char)
    (hs : ∀ c, suffix.head? = some c → c = '_')
    (ht : ∀ fuel, suffix.length ≤ fuel → decode fuel suffix = ([], tail))
    (fuel : Nat) (hf : (escapeChars cs ++ suffix).length ≤ fuel) :
    decode fuel (escapeChars cs ++ suffix) = (cs, tail) := by
  induction cs using escapeChars_induct generalizing fuel with
  | nil => simpa [escapeChars] using ht fuel (by simpa [escapeChars] using hf)
  | x rest ih =>
    rw [escapeChars_x, List.append_assoc] at hf ⊢
    simp only [List.cons_append] at hf ⊢
    have h1 := length_escape_pos '_' ('0' :: 'x' :: (escapeChars rest ++ suffix))
    simp only [List.length_cons] at h1
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
    rw [decode_escape, decode_literals]
    simp [decode, ih fuel (by omega)]
  | v rest ih =>
    rw [escapeChars_v, List.append_assoc] at hf ⊢
    simp only [List.cons_append] at hf ⊢
    have h1 := length_escape_pos '_' ('0' :: 'v' :: (escapeChars rest ++ suffix))
    simp only [List.length_cons] at h1
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
    rw [decode_escape, decode_literals]
    simp [decode, ih fuel (by omega)]
  | t rest ih =>
    rw [escapeChars_t, List.append_assoc] at hf ⊢
    simp only [List.cons_append] at hf ⊢
    have h1 := length_escape_pos '_' ('0' :: 't' :: (escapeChars rest ++ suffix))
    simp only [List.length_cons] at h1
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
    rw [decode_escape, decode_literals]
    simp [decode, ih fuel (by omega)]
  | other c rest hx hv htt ih =>
    rw [escapeChars_other hx hv htt] at hf ⊢
    by_cases hvalid : (c.isAlphanum || decide (c = '_')) = true
    · simp only [hvalid, ↓reduceIte, List.cons_append, List.length_cons] at hf ⊢
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have nomark : ∀ m, m = 'x' ∨ m = 'v' ∨ m = 't' → c = '_' →
          (escapeChars rest ++ suffix).take 2 ≠ ['0', m] := fun m hm hc =>
        no_marker hs (fun r => hx r hc) (fun r => hv r hc) (fun r => htt r hc) m hm
      have n1 : ¬ (c = '_' ∧ (escapeChars rest ++ suffix).take 2 = ['0', 'x']) :=
        fun h => nomark 'x' (by simp) h.1 h.2
      have n2 : ¬ (c = '_' ∧ ((escapeChars rest ++ suffix).take 2 = ['0', 'v'] ∨
          (escapeChars rest ++ suffix).take 2 = ['0', 't'])) := by
        rintro ⟨hc, h | h⟩
        · exact nomark 'v' (by simp) hc h
        · exact nomark 't' (by simp) hc h
      rw [decode]
      simp only [n1, n2, ↓reduceIte]
      simp [ih fuel (by omega)]
    · simp only [hvalid, Bool.false_eq_true, ↓reduceIte] at hf ⊢
      rw [List.append_assoc] at hf ⊢
      have h1 := length_escape_pos c (escapeChars rest ++ suffix)
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [decode_escape]
      simp [ih fuel (by omega)]

private theorem identifier_toList (name : String) :
    (identifier name).toList = match name.toList with
      | [] => ['_', '0', 'x', '_']
      | c :: rest =>
        if c.isDigit || keywords.contains name then escape c ++ escapeChars rest
        else escapeChars (c :: rest) := by
  simp only [identifier, String.toList_ofList]
  rfl

/-- `decode` recovers a name from its identifier followed by any admissible tail. -/
private theorem decode_identifier (name : String) (suffix tail : List Char)
    (hs : ∀ c, suffix.head? = some c → c = '_')
    (ht : ∀ fuel, suffix.length ≤ fuel → decode fuel suffix = ([], tail)) :
    decode ((identifier name).toList ++ suffix).length ((identifier name).toList ++ suffix) =
      (name.toList, tail) := by
  rw [identifier_toList]
  cases hn : name.toList with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.length_cons]
    simp [decode, ht (suffix.length + 3) (by omega)]
  | cons c rest =>
    simp only
    split
    · rw [List.append_assoc]
      have h1 := length_escape_pos c (escapeChars rest ++ suffix)
      obtain ⟨fuel, hfuel⟩ : ∃ k, (escape c ++ (escapeChars rest ++ suffix)).length = k + 1 :=
        ⟨(escape c ++ (escapeChars rest ++ suffix)).length - 1, by omega⟩
      rw [hfuel, decode_escape, decode_escapeChars rest suffix tail hs ht fuel (by omega)]
    · exact decode_escapeChars _ suffix tail hs ht _ (Nat.le_refl _)

private theorem decode_nil (fuel : Nat) : decode fuel [] = ([], []) := by
  cases fuel <;> simp [decode]

/-- Distinct names render as distinct identifiers. -/
theorem identifier_injective {a b : String} (h : identifier a = identifier b) : a = b := by
  have key := fun name => decode_identifier name [] [] (by simp) (fun fuel _ => decode_nil fuel)
  have ha := key a
  rw [h, key b] at ha
  exact String.toList_inj.mp (Prod.mk.inj ha).1.symm

private theorem toString_string' (text : String) : toString text = text := rfl

/-- Whether another variable in `scope` would render the same but for its type and virtuality. -/
private def clash (scope : List Bap.Var) (var : Bap.Var) : Bool :=
  scope.any fun other => other.name = var.name && other.index = var.index && other != var

private def indexChars (index : Nat) : List Char :=
  if index = 0 then [] else '_' :: '0' :: 'v' :: (toString index).toList

private def typeChars (var : Bap.Var) : List Char :=
  (typeCode var.typ ++ if var.isVirtual then "v" else "").toList

private def qualChars (var : Bap.Var) : List Char :=
  '_' :: '0' :: 't' :: (typeCode var.typ ++ if var.isVirtual then "v" else "").toList

private theorem varName_toList (scope : List Bap.Var) (var : Bap.Var) :
    (varName scope var).toList =
      (identifier var.name).toList ++ indexChars var.index ++ if clash scope var then qualChars var else [] := by
  generalize hf : clash scope var = flag
  unfold clash at hf
  unfold varName
  simp only [hf]
  cases flag <;> by_cases h0 : var.index = 0 <;>
    simp [h0, indexChars, qualChars, String.toList_append, toString_string']

/-- A suffix from a marker on is not part of the name. -/
private theorem decode_marker {m : Char} (hm : m = 'v' ∨ m = 't') (rest : List Char) (fuel : Nat)
    (hf : ('_' :: '0' :: m :: rest).length ≤ fuel) :
    decode fuel ('_' :: '0' :: m :: rest) = ([], '_' :: '0' :: m :: rest) := by
  obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
  rcases hm with rfl | rfl <;> simp [decode]

/-- A cut at the first `sep` is unique. -/
private theorem cut_unique {sep : Char} {xs ys q q' : List Char} (hx : ∀ c ∈ xs, c ≠ sep)
    (hy : ∀ c ∈ ys, c ≠ sep) (hq : ∀ c, q.head? = some c → c = sep) (hq' : ∀ c, q'.head? = some c → c = sep)
    (h : xs ++ q = ys ++ q') : xs = ys ∧ q = q' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simpa using h
    | cons y ys =>
      exfalso
      simp only [List.nil_append, List.cons_append] at h
      subst h
      exact hy y (by simp) (hq y (by simp))
  | cons x xs ih =>
    cases ys with
    | nil =>
      exfalso
      simp only [List.nil_append, List.cons_append] at h
      subst h
      exact hx x (by simp) (hq' x (by simp))
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨e, e'⟩ := ih (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc])) h
      exact ⟨by rw [e], e'⟩

private theorem digit_ne {c sep : Char} (hs : sep.isDigit = false) (h : c.isDigit = true) : c ≠ sep := by
  rintro rfl
  simp [h] at hs

private theorem toString_chars {n : Nat} {c : Char} (h : c ∈ (toString n).toList) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
    (by simpa [Nat.toString_eq_ofList_toDigits] using h)

private theorem toString_inj {a b : Nat} (h : (toString a).toList = (toString b).toList) : a = b := by
  have := congrArg (fun chars => (String.ofList chars).toNat?) h
  simp only [String.ofList_toList] at this
  have ra := Nat.toNat?_repr a
  have rb := Nat.toNat?_repr b
  simp only [toString] at this
  rw [rb, ra] at this
  simpa using this

/-- Digits are cut off from what follows them by any non-digit separator. -/
private theorem digits_cut {sep : Char} (hs : sep.isDigit = false) {a b : Nat} {q q' : List Char}
    (hq : ∀ c, q.head? = some c → c = sep) (hq' : ∀ c, q'.head? = some c → c = sep)
    (h : (toString a).toList ++ q = (toString b).toList ++ q') : a = b ∧ q = q' := by
  obtain ⟨e, e'⟩ := cut_unique (sep := sep) (fun c hc => digit_ne hs (toString_chars hc))
    (fun c hc => digit_ne hs (toString_chars hc)) hq hq' h
  exact ⟨toString_inj e, e'⟩

private theorem index_cut {a b : Nat} {q q' : List Char}
    (hq : ∀ c, q.head? = some c → c = '_') (hq' : ∀ c, q'.head? = some c → c = '_')
    (hm : ∀ r, q = '_' :: r → ∃ s, r = '0' :: 't' :: s) (hm' : ∀ r, q' = '_' :: r → ∃ s, r = '0' :: 't' :: s)
    (h : indexChars a ++ q = indexChars b ++ q') : a = b ∧ q = q' := by
  have digit : ('_' : Char).isDigit = false := by decide
  simp only [indexChars] at h
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha; subst hb; simpa using h
  · exfalso
    simp only [ha, hb, ↓reduceIte, List.nil_append, List.cons_append] at h
    obtain ⟨s, hs⟩ := hm _ h
    simp at hs
  · exfalso
    simp only [ha, hb, ↓reduceIte, List.nil_append, List.cons_append] at h
    obtain ⟨s, hs⟩ := hm' _ h.symm
    simp at hs
  · simp only [ha, hb, ↓reduceIte, List.cons_append, List.cons.injEq, true_and] at h
    exact digits_cut digit hq hq' h

private theorem digits10_cut {sep : Char} (hs : sep.isDigit = false) {a b : Nat} {q q' : List Char}
    (hq : ∀ c, q.head? = some c → c = sep) (hq' : ∀ c, q'.head? = some c → c = sep)
    (h : Nat.toDigits 10 a ++ q = Nat.toDigits 10 b ++ q') : a = b ∧ q = q' :=
  digits_cut hs hq hq' (by simpa [Nat.toString_eq_ofList_toDigits] using h)

private theorem digits10_inj {a b : Nat} (h : Nat.toDigits 10 a = Nat.toDigits 10 b) : a = b :=
  toString_inj (by simpa [Nat.toString_eq_ofList_toDigits] using h)

private theorem digits10_ne_v (a b : Nat) : Nat.toDigits 10 a ≠ Nat.toDigits 10 b ++ ['v'] := by
  intro h
  have hv : 'v' ∈ Nat.toDigits 10 a := by simp [h]
  have := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hv
  revert this
  decide

private theorem typeChars_injective {a b : Bap.Var} (h : typeChars a = typeChars b) :
    a.typ = b.typ ∧ a.isVirtual = b.isVirtual := by
  have vdigit : ('v' : Char).isDigit = false := by decide
  have xdigit : ('x' : Char).isDigit = false := by decide
  rcases a with ⟨_, ta, _, va⟩
  rcases b with ⟨_, tb, _, vb⟩
  simp only [typeChars, typeCode, String.toList_append, toString_string'] at h
  cases ta <;> cases tb <;> cases va <;> cases vb <;>
    simp [String.toList_append] at h ⊢
  all_goals first
    | (exfalso; have := digits_cut (sep := 'v') vdigit (a := _) (b := _) (q := []) (q' := ['v']) (by simp) (by simp) (by simpa using h); simp at this; done)
    | (exfalso; have := digits_cut (sep := 'v') vdigit (a := _) (b := _) (q := ['v']) (q' := []) (by simp) (by simp) (by simpa using h); simp at this; done)
    | (exact (digits_cut (sep := 'v') vdigit (q := []) (q' := []) (by simp) (by simp) (by simpa using h)).1)
    | (exact (digits_cut (sep := 'v') vdigit (q := ['v']) (q' := ['v']) (by simp) (by simp) (by simpa using h)).1)
    | skip
  all_goals
    have c := digits10_cut xdigit (by simp) (by simp) h
    have tail := c.2
    simp only [List.cons.injEq, true_and] at tail
  · exact ⟨c.1, digits10_inj tail⟩
  · exact absurd tail (digits10_ne_v _ _)
  · exact absurd tail.symm (digits10_ne_v _ _)
  · exact ⟨c.1, digits10_inj (List.append_cancel_right tail)⟩

/-- Decoding the rendered name recovers the name, and the rest is the index and the qualifier. -/
private theorem varName_decode (scope : List Bap.Var) (var : Bap.Var) :
    decode (varName scope var).toList.length (varName scope var).toList =
      (var.name.toList, indexChars var.index ++ if clash scope var then qualChars var else []) := by
  rw [varName_toList, List.append_assoc]
  apply decode_identifier
  · intro c hc
    simp only [indexChars] at hc
    split at hc
    · split at hc
      · simp [qualChars] at hc; exact hc.symm
      · simp at hc
    · simp at hc; exact hc.symm
  · intro fuel hf
    by_cases h0 : var.index = 0
    · by_cases hc : clash scope var = true
      · simp only [indexChars, h0, ↓reduceIte, hc, List.nil_append, qualChars] at hf ⊢
        exact decode_marker (Or.inr rfl) _ _ hf
      · simp only [indexChars, h0, ↓reduceIte, hc, List.nil_append, Bool.false_eq_true]
        exact decode_nil fuel
    · simp only [indexChars, h0, ↓reduceIte, List.cons_append] at hf ⊢
      exact decode_marker (Or.inl rfl) _ _ hf

/-- The name and index of a variable can be read back from its name in any scope. -/
theorem varName_name_index {scope : List Bap.Var} {a b : Bap.Var} (h : varName scope a = varName scope b) :
    a.name = b.name ∧ a.index = b.index := by
  have ha := varName_decode scope a
  rw [h, varName_decode scope b] at ha
  obtain ⟨hn, hi⟩ := Prod.mk.inj ha
  have q : ∀ v : Bap.Var, ∀ c, (if clash scope v then qualChars v else []).head? = some c → c = '_' := by
    intro v c hc
    split at hc
    · simp [qualChars] at hc; exact hc.symm
    · simp at hc
  have m : ∀ v : Bap.Var, ∀ r, (if clash scope v then qualChars v else []) = '_' :: r →
      ∃ s, r = '0' :: 't' :: s := by
    intro v r hr
    split at hr
    · simp [qualChars] at hr; exact ⟨_, hr.symm⟩
    · simp at hr
  exact ⟨String.toList_inj.mp hn.symm, (index_cut (q b) (q a) (m b) (m a) hi).1.symm⟩

/-- With no other variable of that name and index in sight, the name is the plain one, so most
output does not change. -/
theorem varName_plain {scope : List Bap.Var} {var : Bap.Var} (h : ∀ other ∈ scope, other.name = var.name →
    other.index = var.index → other = var) :
    varName scope var = identifier var.name ++ if var.index = 0 then "" else s!"_0v{var.index}" := by
  have : clash scope var = false := by
    simp only [clash, List.any_eq_false]
    intro other ho
    by_cases hn : other.name = var.name <;> by_cases hi : other.index = var.index <;> simp [hn, hi]
    exact h other ho hn hi
  simp only [clash] at this
  simp [varName, this]

/-- Variables in sight never share a name: every field counts, the type and virtuality too.
Upstream `lib/bap_types/bap_var.ml` compares by ident only, so type and virtuality distinguish
variables here on a clash, which is more than upstream does. -/
theorem varName_injective_in_scope {scope : List Bap.Var} {a b : Bap.Var} (ha : a ∈ scope) (hb : b ∈ scope)
    (h : varName scope a = varName scope b) : a = b := by
  obtain ⟨hn, hidx⟩ := varName_name_index h
  apply Classical.byContradiction
  intro hne
  have ca : clash scope a = true := by
    simp only [clash, List.any_eq_true]
    exact ⟨b, hb, by simp [hn, hidx, Ne.symm hne]⟩
  have cb : clash scope b = true := by
    simp only [clash, List.any_eq_true]
    exact ⟨a, ha, by simp [hn, hidx, hne]⟩
  have e := congrArg String.toList h
  rw [varName_toList, varName_toList, ca, cb, hn, hidx] at e
  simp only [ite_true, List.append_assoc, List.append_cancel_left_eq, qualChars] at e
  simp only [List.cons.injEq, true_and] at e
  obtain ⟨ht, hv⟩ := typeChars_injective (a := a) (b := b) e
  apply hne
  rcases a with ⟨_, _, _, _⟩
  rcases b with ⟨_, _, _, _⟩
  simp_all

/-- Regression: same name and index, told apart by type and by virtuality. -/
theorem varName_clash_examples :
    let a : Bap.Var := ⟨"x", .imm 32, 0, false⟩
    let b : Bap.Var := ⟨"x", .imm 64, 0, false⟩
    let c : Bap.Var := ⟨"x", .imm 64, 0, true⟩
    varName [a, b, c] a = "x_0ti32" ∧ varName [a, b, c] b = "x_0ti64" ∧ varName [a, b, c] c = "x_0ti64v" ∧
      varName [a] a = "x" := by
  decide +kernel

/-! ### Identifier validity -/

private abbrev ValidChar (c : Char) : Prop := c.isAlphanum = true ∨ c = '_'

private theorem hex_valid {c : Char} (h : c ∈ hexChars) : ValidChar c := by
  have : ∀ d ∈ hexChars, d.isAlphanum = true := by decide
  exact Or.inl (this c h)

private theorem escape_valid (c : Char) : ∀ d ∈ escape c, ValidChar d := by
  intro d hd
  simp only [escape, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with ((rfl | rfl | rfl) | hd) | rfl
  · exact Or.inr rfl
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact hex_valid (toDigits16_hex _ d hd)
  · exact Or.inr rfl

private theorem escapeChars_valid (cs : List Char) : ∀ d ∈ escapeChars cs, ValidChar d := by
  have zero : ValidChar '0' := Or.inl (by decide)
  have x : ValidChar 'x' := Or.inl (by decide)
  have v : ValidChar 'v' := Or.inl (by decide)
  have t : ValidChar 't' := Or.inl (by decide)
  induction cs using escapeChars_induct with
  | nil => simp [escapeChars]
  | x r ih =>
    rw [escapeChars_x]
    intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | rfl | hd
    · exact escape_valid _ d hd
    · exact zero
    · exact x
    · exact ih d hd
  | v r ih =>
    rw [escapeChars_v]
    intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | rfl | hd
    · exact escape_valid _ d hd
    · exact zero
    · exact v
    · exact ih d hd
  | t r ih =>
    rw [escapeChars_t]
    intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | rfl | hd
    · exact escape_valid _ d hd
    · exact zero
    · exact t
    · exact ih d hd
  | other c rest hx hv ht ih =>
    rw [escapeChars_other hx hv ht]
    intro d hd
    split at hd
    · rename_i hc
      rcases List.mem_cons.mp hd with rfl | hd
      · simpa using hc
      · exact ih d hd
    · rcases List.mem_append.mp hd with hd | hd
      · exact escape_valid _ d hd
      · exact ih d hd

/-- A rendered identifier only has alphanumeric characters and underscores. -/
theorem identifier_chars (name : String) :
    ∀ c ∈ (identifier name).toList, c.isAlphanum = true ∨ c = '_' := by
  rw [identifier_toList]
  cases name.toList with
  | nil => intro c hc; simp at hc; rcases hc with rfl | rfl | rfl | rfl <;> first | exact Or.inr rfl | exact Or.inl (by decide)
  | cons c rest =>
    simp only
    split
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact escape_valid _ d hd
      · exact escapeChars_valid _ d hd
    · exact escapeChars_valid _

private theorem escapeChars_cons_ne_nil (c : Char) (rest : List Char) :
    escapeChars (c :: rest) ≠ [] := by
  intro h
  have := decode_escapeChars (c :: rest) [] [] (by simp) (fun fuel _ => decode_nil fuel) 0 (by simp [h])
  simp [decode] at this

theorem identifier_nonempty (name : String) : (identifier name).toList ≠ [] := by
  rw [identifier_toList]
  cases name.toList with
  | nil => simp
  | cons c rest =>
    simp only
    split
    · simp [escape]
    · exact escapeChars_cons_ne_nil c rest

/-- A rendered identifier never starts with a digit, so it is a valid C identifier. -/
theorem identifier_no_leading_digit (name : String) (c : Char)
    (h : (identifier name).toList.head? = some c) : c.isDigit = false := by
  rw [identifier_toList] at h
  have under : ('_' : Char).isDigit = false := by decide
  cases hn : name.toList with
  | nil =>
    simp [hn] at h
    subst h; exact under
  | cons d rest =>
    simp only [hn] at h
    split at h
    · simp [escape] at h
      subst h; exact under
    · rename_i hd
      have := head_escapeChars (d :: rest) [] (by simp) c (by simpa using h)
      rcases this with rfl | this
      · exact under
      · simp at this
        subst this
        simp only [Bool.or_eq_true, not_or] at hd
        simpa using hd.1

private theorem escapeChars_of_valid (cs : List Char) (valid : ∀ c ∈ cs, ValidChar c)
    (hx : ¬ ['_', '0', 'x'] <:+: cs) (hv : ¬ ['_', '0', 'v'] <:+: cs) (ht : ¬ ['_', '0', 't'] <:+: cs) :
    escapeChars cs = cs := by
  induction cs using escapeChars_induct with
  | nil => simp [escapeChars]
  | x r _ => exact absurd ⟨[], r, rfl⟩ hx
  | v r _ => exact absurd ⟨[], r, rfl⟩ hv
  | t r _ => exact absurd ⟨[], r, rfl⟩ ht
  | other c rest ex ev et ih =>
    rw [escapeChars_other ex ev et]
    have hc := valid c (by simp)
    have : (c.isAlphanum || decide (c = '_')) = true := by simpa using hc
    simp only [this, ↓reduceIte]
    rw [ih (fun d hd => valid d (by simp [hd]))
      (fun h => hx (h.trans (List.suffix_cons c rest).isInfix))
      (fun h => hv (h.trans (List.suffix_cons c rest).isInfix))
      (fun h => ht (h.trans (List.suffix_cons c rest).isInfix))]

/-- Names which already are valid C identifiers without a marker render as themselves. -/
theorem identifier_of_valid (name : String) (nonempty : name ≠ "")
    (start : ∀ c, name.toList.head? = some c → c.isDigit = false)
    (valid : ∀ c ∈ name.toList, c.isAlphanum = true ∨ c = '_')
    (noEscape : ¬ ['_', '0', 'x'] <:+: name.toList)
    (noIndex : ¬ ['_', '0', 'v'] <:+: name.toList) (noType : ¬ ['_', '0', 't'] <:+: name.toList)
    (notKeyword : name ∉ keywords) : identifier name = name := by
  apply String.toList_inj.mp
  rw [identifier_toList]
  cases hn : name.toList with
  | nil => exact absurd (String.toList_inj.mp (by simpa using hn)) nonempty
  | cons c rest =>
    have hc : c.isDigit = false := start c (by simp [hn])
    have hk : keywords.contains name = false := by simpa using notKeyword
    simp only [hc, hk, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    rw [hn] at valid noEscape noIndex noType
    exact escapeChars_of_valid _ valid noEscape noIndex noType

/-- What `decode` undoes also says `escapeChars` itself loses nothing. -/
private theorem escapeChars_injective {a b : List Char} (h : escapeChars a = escapeChars b) : a = b := by
  have key := fun cs => decode_escapeChars cs [] [] (by simp) (fun fuel _ => decode_nil fuel)
    (escapeChars cs ++ []).length (Nat.le_refl _)
  have ha := key a
  simp only [List.append_nil] at ha
  rw [h] at ha
  have hb := key b
  simp only [List.append_nil] at hb
  rw [hb] at ha
  exact (Prod.mk.inj ha).1.symm

private theorem keywords_fixed :
    keywords.all (fun k => decide (escapeChars k.toList = k.toList)) = true := by
  decide +kernel

private theorem keywords_no_escape :
    keywords.all (fun k => decide (k.toList.take 3 ≠ ['_', '0', 'x'])) = true := by
  decide +kernel

/-- Keywords never survive: the rendering of any name, keywords included, is not a C keyword. -/
theorem identifier_not_keyword (name : String) : identifier name ∉ keywords := by
  intro hk
  have fixed := List.all_eq_true.mp keywords_fixed _ hk
  have noesc := List.all_eq_true.mp keywords_no_escape _ hk
  simp only [decide_eq_true_eq] at fixed noesc
  have hl := identifier_toList name
  cases hn : name.toList with
  | nil =>
    rw [hn] at hl
    simp only at hl
    rw [hl] at noesc
    simp at noesc
  | cons c rest =>
    rw [hn] at hl
    simp only at hl
    split at hl
    · rw [hl] at noesc
      simp [escape] at noesc
    · rename_i hd
      simp only [Bool.or_eq_true, not_or] at hd
      have : escapeChars (identifier name).toList = escapeChars name.toList := by
        rw [fixed, hl, hn]
      have e := escapeChars_injective this
      have en : identifier name = name := String.toList_inj.mp e
      rw [en] at hk
      exact hd.2 (by simpa using hk)

theorem identifier_int : identifier "int" = "_0x69_nt" := by decide +kernel

theorem identifier_rax : identifier "RAX" = "RAX" := by decide +kernel

private theorem digit_valid {c : Char} (h : c.isDigit = true) : c.isAlphanum = true := by
  simp [Char.isAlphanum, h]

private theorem qualChars_valid (var : Bap.Var) : ∀ c ∈ qualChars var, ValidChar c := by
  intro c hc
  simp only [qualChars, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | hc
  · exact Or.inr rfl
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · rw [String.toList_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases var with ⟨_, typ, _, _⟩
      cases typ <;> simp [typeCode, toString_string', String.toList_append] at hc
      · subst hc; exact Or.inl (by decide)
      · subst hc; exact Or.inl (by decide)
      · rcases hc with rfl | hc | rfl | hc
        · exact Or.inl (by decide)
        · exact Or.inl (digit_valid (toString_chars (by simpa using hc)))
        · exact Or.inl (by decide)
        · exact Or.inl (digit_valid (toString_chars (by simpa using hc)))
      · rcases hc with rfl | hc
        · exact Or.inl (by decide)
        · exact Or.inl (digit_valid (toString_chars (by simpa using hc)))
    · split at hc
      · simp at hc; subst hc; exact Or.inl (by decide)
      · simp at hc

theorem varName_chars (scope : List Bap.Var) (var : Bap.Var) :
    ∀ c ∈ (varName scope var).toList, c.isAlphanum = true ∨ c = '_' := by
  rw [varName_toList]
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact identifier_chars _ c hc
  · simp only [indexChars] at hc
    split at hc
    · simp at hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | rfl | hc
      · exact Or.inr rfl
      · exact Or.inl (by decide)
      · exact Or.inl (by decide)
      · exact Or.inl (digit_valid (toString_chars hc))
  · split at hc
    · exact qualChars_valid var c hc
    · simp at hc

theorem indentation_toList (level : Nat) : (indentation level).toList = List.replicate level ' ' := by
  simp [indentation]

theorem indentation_length (level : Nat) : (indentation level).length = level := by
  simp [← String.length_toList, indentation_toList]

theorem indentation_add (left right : Nat) :
    indentation (left + right) = indentation left ++ indentation right := by
  apply String.toList_inj.mp
  simp [indentation_toList, List.replicate_append_replicate]

/-! ### Bracket structure of rendered text -/

/-- Stack machine accepting properly nested round and curly brackets. -/
def scan : List Char → List Char → Option (List Char)
  | stack, [] => some stack
  | stack, c :: rest =>
    if c = '(' ∨ c = '{' then scan (c :: stack) rest
    else if c = ')' then
      match stack with
      | '(' :: stack => scan stack rest
      | _ => none
    else if c = '}' then
      match stack with
      | '{' :: stack => scan stack rest
      | _ => none
    else scan stack rest

/-- Round and curly brackets of `text` nest properly, whatever is already open around it. -/
def Balanced (text : String) : Prop := ∀ stack, scan stack text.toList = some stack

private theorem toString_string (text : String) : toString text = text := rfl

theorem scan_append (stack : List Char) (left right : List Char) :
    scan stack (left ++ right) = (scan stack left).bind fun stack => scan stack right := by
  induction left generalizing stack with
  | nil => simp [scan]
  | cons c rest ih =>
    simp only [List.cons_append, scan]
    split
    · exact ih _
    · split
      · split
        · exact ih _
        · rfl
      · split
        · split
          · exact ih _
          · rfl
        · exact ih _

private abbrev scanS (stack : List Char) (text : String) := scan stack text.toList

private theorem scanS_append (stack : List Char) (left right : String) :
    scanS stack (left ++ right) = (scanS stack left).bind fun stack => scanS stack right := by
  simp [scanS, scan_append]

theorem Balanced.append {left right : String} (hl : Balanced left) (hr : Balanced right) :
    Balanced (left ++ right) := by
  intro stack
  simp [String.toList_append, scan_append, hl stack, hr stack]

/-- Text without brackets is balanced. -/
theorem balanced_of_no_brackets {text : String}
    (h : ∀ c ∈ text.toList, c ≠ '(' ∧ c ≠ '{' ∧ c ≠ ')' ∧ c ≠ '}') : Balanced text := by
  intro stack
  generalize text.toList = chars at h
  induction chars generalizing stack with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨h1, h2, h3, h4⟩ := h c (by simp)
    simp [scan, h1, h2, h3, h4]
    exact ih stack (fun d hd => h d (by simp [hd]))

theorem balanced_wrap_round {inner : String} (h : Balanced inner) :
    Balanced ("(" ++ inner ++ ")") := by
  intro stack
  simp [String.toList_append, scan_append, scan, h ('(' :: stack)]

theorem balanced_wrap_curly {inner : String} (h : Balanced inner) :
    Balanced ("{" ++ inner ++ "}") := by
  intro stack
  simp [String.toList_append, scan_append, scan, h ('{' :: stack)]

private theorem digitChar_no_bracket (d : Nat) :
    d.digitChar ≠ '(' ∧ d.digitChar ≠ '{' ∧ d.digitChar ≠ ')' ∧ d.digitChar ≠ '}' := by
  have step : ∀ (p : Prop) [Decidable p] (t e : Char), t ∈ "0123456789abcdef*".toList →
      e ∈ "0123456789abcdef*".toList → (if p then t else e) ∈ "0123456789abcdef*".toList := by
    intro p _ t e ht he
    split <;> assumption
  have cases : d.digitChar ∈ "0123456789abcdef*".toList := by
    unfold Nat.digitChar
    repeat (first | decide | apply step)
  have check : ∀ c ∈ "0123456789abcdef*".toList, c ≠ '(' ∧ c ≠ '{' ∧ c ≠ ')' ∧ c ≠ '}' := by decide
  exact check _ cases

private theorem mem_toDigitsCore {base fuel n : Nat} {cs : List Char} {c : Char}
    (h : c ∈ Nat.toDigitsCore base fuel n cs) : c ∈ cs ∨ ∃ d : Nat, c = d.digitChar := by
  induction fuel generalizing n cs with
  | zero => exact Or.inl (by simpa [Nat.toDigitsCore] using h)
  | succ fuel ih =>
    rw [Nat.toDigitsCore] at h
    split at h
    · simp at h
      rcases h with rfl | h
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl h
    · rcases ih h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl h
      · exact Or.inr h

private theorem mem_toDigits {base n : Nat} {c : Char} (h : c ∈ Nat.toDigits base n) :
    ∃ d : Nat, c = d.digitChar := by
  rcases mem_toDigitsCore (by simpa [Nat.toDigits] using h) with h | h
  · simp at h
  · exact h

theorem balanced_toString_nat (n : Nat) : Balanced (toString n) := by
  apply balanced_of_no_brackets
  intro c hc
  obtain ⟨d, rfl⟩ := mem_toDigits (by simpa using hc)
  exact digitChar_no_bracket d

theorem balanced_hex (n : Nat) : Balanced (hex n) := by
  apply balanced_of_no_brackets
  intro c hc
  obtain ⟨d, rfl⟩ := mem_toDigits (by simpa [hex] using hc)
  exact digitChar_no_bracket d

theorem balanced_identifier (name : String) : Balanced (identifier name) := by
  apply balanced_of_no_brackets
  intro c hc
  rcases identifier_chars name c hc with h | rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)
  · decide

theorem balanced_varName (scope : List Bap.Var) (var : Bap.Var) : Balanced (varName scope var) := by
  apply balanced_of_no_brackets
  intro c hc
  rcases varName_chars scope var c hc with h | rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)
  · decide

theorem balanced_indentation (level : Nat) : Balanced (indentation level) := by
  apply balanced_of_no_brackets
  intro c hc
  rw [indentation_toList] at hc
  rw [List.eq_of_mem_replicate hc]
  decide

theorem balanced_endianName (endian : Bap.Endian) : Balanced (endianName endian) := by
  cases endian <;> (intro stack; simp [endianName, scan])

theorem balanced_binName (op : BinOp) : Balanced (binName op) := by
  cases op <;> (intro stack; simp [binName, scan])

theorem balanced_signedBinName {op : BinOp} {name : String} (h : signedBinName op = some name) :
    Balanced name := by
  cases op <;> simp [signedBinName] at h <;> subst h <;> (intro stack; simp [scan])

/-- Messages of the `unknown` leaves of an expression, the only free text `exp` renders. -/
def messages : Exp → List String
  | .int _ | .var _ => []
  | .load memory address _ _ => messages memory ++ messages address
  | .store memory address value _ _ => messages memory ++ messages address ++ messages value
  | .bin _ left right | .concat left right => messages left ++ messages right
  | .un _ value | .cast _ _ value | .extract _ _ value => messages value
  | .letIn _ value body => messages value ++ messages body
  | .ite condition yes no => messages condition ++ messages yes ++ messages no
  | .unknown message _ => [message]

private theorem scan_digits (base n : Nat) (stack : List Char) :
    scan stack (Nat.toDigits base n) = some stack := by
  have h := balanced_of_no_brackets (text := String.ofList (Nat.toDigits base n))
    (fun c hc => by
      obtain ⟨d, rfl⟩ := mem_toDigits (by simpa using hc)
      exact digitChar_no_bracket d) stack
  simpa using h

theorem balanced_ctype (typ : Bap.Typ) : Balanced (ctype typ) := by
  unfold ctype
  split <;> (intro stack; simp [toString_string, String.toList_append, scan_append, scan, scan_digits])

/-- A literal's width is written with brackets that nest. -/
theorem balanced_withWidth (e : Exp) {rendered : String} (h : Balanced rendered) : Balanced (withWidth e rendered) := by
  cases e with
  | @int w value =>
    intro stack
    have ht := balanced_ctype (.imm w)
    simp [withWidth, toString_string, String.toList_append, scan_append, scan, ht _, h _]
  | _ => exact h

theorem balanced_leftOperand (op : BinOp) (left right : Exp) {rendered : String} (h : Balanced rendered) :
    Balanced (leftOperand op left right rendered) := by
  unfold leftOperand
  split
  · exact balanced_withWidth left h
  · exact h

/-- Round and curly brackets of `exp` always nest properly when the free text does. -/
theorem expIn_balanced (scope : List Bap.Var) (e : Exp) (h : ∀ m ∈ messages e, Balanced (quote m)) :
    Balanced (expIn scope e) := by
  induction e with
  | int value =>
    intro stack
    simp [toString_string, expIn, String.toList_append, scan, hex, scan_digits]
  | var var => simpa [expIn] using balanced_varName scope var
  | load memory address endian size ihm iha =>
    have hm := ihm fun m hm => h m (by simp [messages, hm])
    have ha := iha fun m hm => h m (by simp [messages, hm])
    have he := balanced_endianName endian
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, scan_digits, hm _, ha _, he _]
  | store memory address value endian size ihm iha ihv =>
    have hm := ihm fun m hm => h m (by simp [messages, hm])
    have ha := iha fun m hm => h m (by simp [messages, hm])
    have hv := ihv fun m hm => h m (by simp [messages, hm])
    have he := balanced_endianName endian
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, scan_digits, hm _, ha _, hv _, he _]
  | bin op left right ihl ihr =>
    have hl := balanced_leftOperand op left right (ihl fun m hm => h m (by simp [messages, hm]))
    have hr := ihr fun m hm => h m (by simp [messages, hm])
    intro stack
    cases hs : signedBinName op with
    | none =>
      have hb := balanced_binName op
      simp [toString_string, expIn, hs, String.toList_append, scan_append, scan, hl _, hr _, hb _]
    | some name =>
      have hn := balanced_signedBinName hs
      simp [toString_string, expIn, hs, String.toList_append, scan_append, scan, hl _, hr _, hn _]
  | un op value ih =>
    have hv := balanced_withWidth value (ih fun m hm => h m (by simp [messages, hm]))
    intro stack
    cases op <;> simp [toString_string, expIn, unName, String.toList_append, scan_append, scan, hv _]
  | cast kind width value ih =>
    have hv := balanced_withWidth value (ih fun m hm => h m (by simp [messages, hm]))
    intro stack
    cases kind <;> simp [toString_string, expIn, castName, String.toList_append, scan_append, scan, scan_digits, hv _]
  | letIn var value body ihv ihb =>
    have hv := ihv fun m hm => h m (by simp [messages, hm])
    have hb := ihb fun m hm => h m (by simp [messages, hm])
    have hn := balanced_varName scope var
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, hv _, hb _, hn _]
  | ite condition yes no ihc ihy ihn =>
    have hc := ihc fun m hm => h m (by simp [messages, hm])
    have hy := ihy fun m hm => h m (by simp [messages, hm])
    have hn := ihn fun m hm => h m (by simp [messages, hm])
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, hc _, hy _, hn _]
  | extract high low value ih =>
    have hv := balanced_withWidth value (ih fun m hm => h m (by simp [messages, hm]))
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, scan_digits, hv _]
  | concat left right ihl ihr =>
    have hl := balanced_withWidth left (ihl fun m hm => h m (by simp [messages, hm]))
    have hr := balanced_withWidth right (ihr fun m hm => h m (by simp [messages, hm]))
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, hl _, hr _]
  | unknown message typ =>
    have hq := h message (by simp [messages])
    have ht := balanced_ctype typ
    intro stack
    simp [toString_string, expIn, String.toList_append, scan_append, scan, hq _, ht _]

theorem exp_balanced (e : Exp) (h : ∀ m ∈ messages e, Balanced (quote m)) : Balanced (exp e) :=
  expIn_balanced _ e h

/-- A bracket in free text is rendered verbatim inside a C string, so bare bracket balance
of `exp` needs the side condition of `exp_balanced`. -/
theorem exp_unknown_unbalanced (typ : Bap.Typ) : ¬ Balanced (exp (.unknown "(" typ)) := by
  intro h
  have hq : (quote "(").toList = ['"', '(', '"'] := by
    simp only [quote, Bap.Sexp.render, needsQuotes]
    decide
  have := h []
  simp [toString_string, exp, expIn, String.toList_append, scan_append, scan, hq, balanced_ctype typ _] at this

theorem quote_balanced_of_no_brackets {message : String}
    (h : ∀ c ∈ message.toList, c ≠ '(' ∧ c ≠ '{' ∧ c ≠ ')' ∧ c ≠ '}') : Balanced (quote message) := by
  apply balanced_of_no_brackets
  intro c hc
  simp only [quote, Bap.Sexp.render] at hc
  split at hc
  · simp [String.toList_append] at hc
    rcases hc with rfl | ⟨d, hd, hc⟩ | rfl
    · decide
    · obtain ⟨h1, h2, h3, h4⟩ := h d hd
      revert hc
      unfold Sexp.escape
      split <;> simp <;> first | (rintro (rfl | rfl) <;> decide) | (rintro rfl; exact ⟨h1, h2, h3, h4⟩)
    · decide
  · exact h c hc

/-- Unknown-free expressions always render with properly nested brackets. -/
theorem exp_balanced_of_no_messages (e : Exp) (h : messages e = []) : Balanced (exp e) :=
  exp_balanced e (by simp [h])

/-! ### Line structure -/

private theorem digitChar_ne_newline (d : Nat) : d.digitChar ≠ '\n' := by
  have step : ∀ (p : Prop) [Decidable p] (t e : Char), t ≠ '\n' → e ≠ '\n' →
      (if p then t else e) ≠ '\n' := by
    intro p _ t e ht he
    split <;> assumption
  unfold Nat.digitChar
  repeat (first | decide | apply step)

private theorem no_newline_digits (base n : Nat) : '\n' ∉ Nat.toDigits base n := by
  intro h
  obtain ⟨d, hd⟩ := mem_toDigits h
  exact digitChar_ne_newline d hd.symm

private theorem no_newline_varName (scope : List Bap.Var) (var : Bap.Var) : '\n' ∉ (varName scope var).toList := by
  intro h
  have : ∀ c : Char, c = '\n' → ¬ (c.isAlphanum = true ∨ c = '_') := by
    rintro c rfl; decide
  exact this _ rfl (varName_chars scope var _ h)

private theorem no_newline_quote (message : String) : '\n' ∉ (quote message).toList := by
  simp only [quote, Bap.Sexp.render]
  split
  · simp [String.toList_append]
    intro d _
    by_cases hd : d = '\n'
    · subst hd; decide
    · unfold Sexp.escape
      split <;> simp [Ne.symm hd]
  · rename_i h
    intro hm
    simp only [needsQuotes, decide_eq_true_eq, not_or, Bool.not_eq_true] at h
    have := List.any_eq_false.mp h.2.2 _ hm
    exact this (by decide)

private theorem no_newline_ctype (typ : Bap.Typ) : '\n' ∉ (ctype typ).toList := by
  unfold ctype
  split <;> simp [toString_string, String.toList_append, no_newline_digits]

/-- Free text is escaped and names are sanitised, so an expression renders on one line. -/
theorem no_newline_withWidth (e : Exp) {rendered : String} (h : '\n' ∉ rendered.toList) :
    '\n' ∉ (withWidth e rendered).toList := by
  cases e with
  | int value => simp [withWidth, toString_string, String.toList_append, no_newline_ctype, h]
  | _ => exact h

theorem no_newline_leftOperand (op : BinOp) (left right : Exp) {rendered : String} (h : '\n' ∉ rendered.toList) :
    '\n' ∉ (leftOperand op left right rendered).toList := by
  unfold leftOperand
  split
  · exact no_newline_withWidth left h
  · exact h

theorem expIn_no_newline (scope : List Bap.Var) (e : Exp) : '\n' ∉ (expIn scope e).toList := by
  induction e with
  | int value => simp [toString_string, expIn, String.toList_append, hex, no_newline_digits]
  | var var => simpa [expIn] using no_newline_varName scope var
  | load memory address endian size ihm iha =>
    cases endian <;>
      simp [toString_string, expIn, endianName, String.toList_append, no_newline_digits, ihm, iha]
  | store memory address value endian size ihm iha ihv =>
    cases endian <;>
      simp [toString_string, expIn, endianName, String.toList_append, no_newline_digits, ihm, iha, ihv]
  | bin op left right ihl ihr =>
    have hl := no_newline_leftOperand op left right ihl
    cases op <;> simp [toString_string, expIn, signedBinName, binName, String.toList_append, hl, ihr]
  | un op value ih =>
    have hv := no_newline_withWidth value ih
    cases op <;> simp [toString_string, expIn, unName, String.toList_append, hv]
  | cast kind width value ih =>
    have hv := no_newline_withWidth value ih
    cases kind <;>
      simp [toString_string, expIn, castName, String.toList_append, no_newline_digits, hv]
  | letIn var value body ihv ihb =>
    simp [toString_string, expIn, String.toList_append, no_newline_varName scope, ihv, ihb]
  | ite condition yes no ihc ihy ihn =>
    simp [toString_string, expIn, String.toList_append, ihc, ihy, ihn]
  | extract high low value ih =>
    simp [toString_string, expIn, String.toList_append, no_newline_digits, no_newline_withWidth value ih]
  | concat left right ihl ihr =>
    simp [toString_string, expIn, String.toList_append, no_newline_withWidth left ihl, no_newline_withWidth right ihr]
  | unknown message typ =>
    simp [toString_string, expIn, String.toList_append, no_newline_quote, no_newline_ctype]

theorem exp_no_newline (e : Exp) : '\n' ∉ (exp e).toList := expIn_no_newline _ e

private def writeText (scope : List Bap.Var) (memory address value : Exp) (endian : Bap.Endian) (size : Nat) : String :=
  s!"write{size * 8}_{endianName endian}({expIn scope memory}, {expIn scope address}, {expIn scope value});"

/-- Whether a store updates the memory variable it reads. -/
private def inPlace (var : Bap.Var) : Exp → Bool
  | .var source => source = var
  | _ => false

private theorem stmt_store_eq (scope : List Bap.Var) (level : Nat) (var : Bap.Var) (memory address value : Exp)
    (endian : Bap.Endian) (size : Nat) :
    stmtIn scope level (.move var (.store memory address value endian size)) =
      if inPlace var memory then indentation level ++ writeText scope memory address value endian size
      else indentation level ++ varName scope var ++ " = " ++ writeText scope memory address value endian size := by
  rw [stmtIn.eq_def]
  simp only [writeText, inPlace]
  cases memory <;> rfl

private theorem no_newline_writeText (scope : List Bap.Var) (memory address value : Exp) (endian : Bap.Endian) (size : Nat) :
    '\n' ∉ (writeText scope memory address value endian size).toList := by
  cases endian <;> simp [writeText, toString_string, endianName, String.toList_append,
    no_newline_digits, expIn_no_newline]

/-- Statements without nested blocks render as exactly one line. -/
theorem stmtIn_single_line (scope : List Bap.Var) (level : Nat) (s : Stmt)
    (h : match s with | .while _ _ | .ifElse _ _ _ => False | _ => True) :
    '\n' ∉ (stmtIn scope level s).toList := by
  have hi : '\n' ∉ (indentation level).toList := by
    rw [indentation_toList]
    intro hm
    exact absurd (List.eq_of_mem_replicate hm) (by decide)
  cases s with
  | move var value =>
    cases value with
    | store memory address value endian size =>
      rw [stmt_store_eq]
      split <;> simp [String.toList_append, hi, no_newline_varName scope, no_newline_writeText]
    | _ => simp [toString_string, stmtIn, String.toList_append, no_newline_varName scope, hi, expIn_no_newline]
  | jmp target =>
    cases target with
    | int value => simp [toString_string, stmtIn, String.toList_append, hex, no_newline_digits, hi]
    | _ => simp [toString_string, stmtIn, String.toList_append, hi, expIn_no_newline]
  | special message => simp [toString_string, stmtIn, String.toList_append, hi, no_newline_quote]
  | cpuExn number => simp [toString_string, stmtIn, String.toList_append, hi, no_newline_digits]
  | «while» condition body => exact h.elim
  | ifElse condition yes no => exact h.elim

theorem stmt_single_line (level : Nat) (s : Stmt)
    (h : match s with | .while _ _ | .ifElse _ _ _ => False | _ => True) :
    '\n' ∉ (stmt level s).toList := stmtIn_single_line _ level s h

/-! ### Statements -/

/-- Every `unknown` message anywhere in a statement renders to balanced text. -/
inductive StmtBalanced : Stmt → Prop where
  | move (var value) : (∀ m ∈ messages value, Balanced (quote m)) → StmtBalanced (.move var value)
  | jmp (target) : (∀ m ∈ messages target, Balanced (quote m)) → StmtBalanced (.jmp target)
  | special (message) : Balanced (quote message) → StmtBalanced (.special message)
  | cpuExn (number) : StmtBalanced (.cpuExn number)
  | while_ (condition body) : (∀ m ∈ messages condition, Balanced (quote m)) →
      (∀ s ∈ body, StmtBalanced s) → StmtBalanced (.while condition body)
  | ifElse (condition yes no) : (∀ m ∈ messages condition, Balanced (quote m)) →
      (∀ s ∈ yes, StmtBalanced s) → (∀ s ∈ no, StmtBalanced s) →
      StmtBalanced (.ifElse condition yes no)

theorem balanced_intercalate {separator : String} {items : List String}
    (hs : Balanced separator) (hi : ∀ item ∈ items, Balanced item) :
    Balanced (String.intercalate separator items) := by
  induction items with
  | nil => intro stack; simp [scan]
  | cons head tail ih =>
    cases tail with
    | nil => simpa using hi head (by simp)
    | cons next tail =>
      rw [String.intercalate_cons_cons, String.append_assoc]
      refine (hi head (by simp)).append (hs.append ?_)
      exact ih fun item hm => hi item (by simp [hm])

private theorem exp_scan (scope : List Bap.Var) {e : Exp} (h : ∀ m ∈ messages e, Balanced (quote m)) (stack : List Char) :
    scan stack (expIn scope e).toList = some stack := expIn_balanced scope e h stack

/-- A statement renders with properly nested brackets when its free text does. -/
theorem stmtIn_balanced (scope : List Bap.Var) {s : Stmt} (h : StmtBalanced s) (level : Nat) :
    Balanced (stmtIn scope level s) := by
  induction h generalizing level with
  | move var value hv =>
    have hi := balanced_indentation level
    cases value with
    | store memory address value endian size =>
      have hm := exp_scan scope (e := memory) fun m hm => hv m (by simp [messages, hm])
      have ha := exp_scan scope (e := address) fun m hm => hv m (by simp [messages, hm])
      have hw := exp_scan scope (e := value) fun m hm => hv m (by simp [messages, hm])
      have he := balanced_endianName endian
      have hn := balanced_varName scope var
      have hwrite : Balanced (writeText scope memory address value endian size) := by
        intro stack
        simp [writeText, toString_string, String.toList_append, scan_append, scan, scan_digits,
          hm _, ha _, hw _, he _]
      rw [stmt_store_eq]
      intro stack
      split <;> simp [String.toList_append, scan_append, scan, hi _, hn _, hwrite _]
    | _ =>
      have he := exp_scan scope hv
      have hn := balanced_varName scope var
      intro stack
      simp [toString_string, stmtIn, String.toList_append, scan_append, scan, hi _, hn _, he _]
  | jmp target ht =>
    have hi := balanced_indentation level
    cases target with
    | int value =>
      intro stack
      simp [toString_string, stmtIn, String.toList_append, scan_append, scan, hi _, hex, scan_digits]
    | _ =>
      have he := exp_scan scope ht
      intro stack
      simp [toString_string, stmtIn, String.toList_append, scan_append, scan, hi _, he _]
  | special message hq =>
    have hi := balanced_indentation level
    intro stack
    simp [toString_string, stmtIn, String.toList_append, scan_append, scan, hi _, hq _]
  | cpuExn number =>
    have hi := balanced_indentation level
    intro stack
    simp [toString_string, stmtIn, String.toList_append, scan_append, scan, scan_digits, hi _]
  | while_ condition body hc _ ih =>
    have hi := balanced_indentation level
    have he := exp_scan scope hc
    have hb : Balanced (String.intercalate "\n" (body.map (stmtIn scope (level + 2)))) :=
      balanced_intercalate (by intro stack; simp [scan]) (by
        intro item hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
        exact ih s hs _)
    intro stack
    have hb' : ∀ st, scan st (['\n'].intercalate (List.map (String.toList ∘ stmtIn scope (level + 2)) body))
        = some st := fun st => by simpa using hb st
    simp only [stmtIn, String.toList_append, scan_append]
    simp [scan, hi _, he _, hb' _]
  | ifElse condition yes no hc _ _ ihy ihn =>
    have hi := balanced_indentation level
    have he := exp_scan scope hc
    have hy : Balanced (String.intercalate "\n" (yes.map (stmtIn scope (level + 2)))) :=
      balanced_intercalate (by intro stack; simp [scan]) (by
        intro item hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
        exact ihy s hs _)
    have hn : Balanced (String.intercalate "\n" (no.map (stmtIn scope (level + 2)))) :=
      balanced_intercalate (by intro stack; simp [scan]) (by
        intro item hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
        exact ihn s hs _)
    intro stack
    have hy' : ∀ st, scan st (['\n'].intercalate (List.map (String.toList ∘ stmtIn scope (level + 2)) yes))
        = some st := fun st => by simpa using hy st
    simp only [stmtIn, String.toList_append, scan_append]
    cases no with
    | nil => simp [scan, hi _, he _, hy' _]
    | cons head tail =>
      have hn' : ∀ st, scan st (['\n'].intercalate
          ((stmtIn scope (level + 2) head).toList :: List.map (String.toList ∘ stmtIn scope (level + 2)) tail))
          = some st := fun st => by simpa using hn st
      simp [scan, scan_append, hi _, he _, hy' _, hn' _]

theorem stmt_balanced {s : Stmt} (h : StmtBalanced s) (level : Nat) : Balanced (stmt level s) :=
  stmtIn_balanced _ h level

/-- Every statement starts with its own indentation. -/
theorem stmtIn_prefix (scope : List Bap.Var) (level : Nat) (s : Stmt) :
    (indentation level).toList <+: (stmtIn scope level s).toList := by
  cases s with
  | move var value =>
    cases value with
    | store memory address value endian size =>
      rw [stmt_store_eq]
      split <;> simp [String.toList_append]
    | _ => simp [toString_string, stmtIn, String.toList_append]
  | jmp target => cases target <;> simp [toString_string, stmtIn, String.toList_append]
  | special message => simp [toString_string, stmtIn, String.toList_append]
  | cpuExn number => simp [toString_string, stmtIn, String.toList_append]
  | «while» condition body => simp [stmtIn, String.toList_append]
  | ifElse condition yes no => simp [stmtIn, String.toList_append]

theorem stmt_prefix (level : Nat) (s : Stmt) :
    (indentation level).toList <+: (stmt level s).toList := stmtIn_prefix _ level s

theorem stmt_eq_indentation_append (level : Nat) (s : Stmt) :
    ∃ rest, stmt level s = indentation level ++ rest := by
  obtain ⟨rest, h⟩ := stmt_prefix level s
  refine ⟨String.ofList rest, String.toList_inj.mp ?_⟩
  simpa [String.toList_append] using h.symm

/-- Statements without nested blocks only shift when indented further. -/
theorem stmtIn_shift (scope : List Bap.Var) (level extra : Nat) (s : Stmt)
    (h : match s with | .while _ _ | .ifElse _ _ _ => False | _ => True) :
    stmtIn scope (extra + level) s = indentation extra ++ stmtIn scope level s := by
  cases s with
  | move var value =>
    cases value with
    | store memory address value endian size =>
      simp only [stmt_store_eq]
      split <;> simp [indentation_add, String.append_assoc]
    | _ => simp [toString_string, stmtIn, indentation_add, String.append_assoc]
  | jmp target => cases target <;> simp [toString_string, stmtIn, indentation_add, String.append_assoc]
  | special message => simp [toString_string, stmtIn, indentation_add, String.append_assoc]
  | cpuExn number => simp [toString_string, stmtIn, indentation_add, String.append_assoc]
  | «while» condition body => exact h.elim
  | ifElse condition yes no => exact h.elim

theorem stmt_shift (level extra : Nat) (s : Stmt)
    (h : match s with | .while _ _ | .ifElse _ _ _ => False | _ => True) :
    stmt (extra + level) s = indentation extra ++ stmt level s := stmtIn_shift _ level extra s h

/-- The statements of a body at the indentation of a function, with names from `scope`. -/
private def bodyIn (scope : List Bap.Var) (code : List Stmt) : String :=
  String.intercalate "\n" (code.map (stmtIn scope 2))

private theorem program_eq (code : List Stmt) : program code = bodyIn (code.flatMap stmtVars).eraseDups code := rfl

theorem program_nil : program [] = "" := by simp [program]

private theorem bodyIn_cons_cons (scope : List Bap.Var) (head next : Stmt) (tail : List Stmt) :
    bodyIn scope (head :: next :: tail) = stmtIn scope 2 head ++ "\n" ++ bodyIn scope (next :: tail) := by
  simp [bodyIn, String.intercalate_cons_cons, String.append_assoc]

/-- A program's first statement and the rest share one scope, so names agree across statements. -/
theorem program_cons_cons (head next : Stmt) (tail : List Stmt) :
    program (head :: next :: tail) =
      stmtIn ((head :: next :: tail).flatMap stmtVars).eraseDups 2 head ++ "\n" ++
        String.intercalate "\n" ((next :: tail).map (stmtIn ((head :: next :: tail).flatMap stmtVars).eraseDups 2)) :=
  bodyIn_cons_cons _ head next tail

private theorem bodyIn_balanced (scope : List Bap.Var) {code : List Stmt} (h : ∀ s ∈ code, StmtBalanced s) :
    Balanced (bodyIn scope code) :=
  balanced_intercalate (by intro stack; simp [scan]) (by
    intro item hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    exact stmtIn_balanced scope (h s hs) _)

theorem program_balanced {code : List Stmt} (h : ∀ s ∈ code, StmtBalanced s) :
    Balanced (program code) :=
  bodyIn_balanced _ h

/-! ### Names of a rendered unit -/

/-- All the variables of a program are in the scope its statements are rendered with, and no two of
them render with the same name. -/
theorem program_names_injective {code : List Stmt} {a b : Bap.Var} (ha : a ∈ code.flatMap stmtVars)
    (hb : b ∈ code.flatMap stmtVars)
    (h : varName (code.flatMap stmtVars).eraseDups a = varName (code.flatMap stmtVars).eraseDups b) : a = b :=
  varName_injective_in_scope (List.mem_eraseDups.mpr ha) (List.mem_eraseDups.mpr hb) h

theorem function_names_injective {params : List Bap.Var} {code : List Stmt} {a b : Bap.Var}
    (ha : a ∈ params ++ code.flatMap stmtVars) (hb : b ∈ params ++ code.flatMap stmtVars)
    (h : varName (params ++ code.flatMap stmtVars).eraseDups a =
      varName (params ++ code.flatMap stmtVars).eraseDups b) : a = b :=
  varName_injective_in_scope (List.mem_eraseDups.mpr ha) (List.mem_eraseDups.mpr hb) h

theorem exp_var_in_scope {value : Exp} {x : Bap.Var} (h : x ∈ expVars value) : x ∈ (expVars value).eraseDups :=
  List.mem_eraseDups.mpr h

/-- Every destination and every read variable of a statement is in its scope. -/
theorem stmt_move_in_scope (var : Bap.Var) (value : Exp) {x : Bap.Var} (h : x = var ∨ x ∈ expVars value) :
    x ∈ (stmtVars (.move var value)).eraseDups := by
  apply List.mem_eraseDups.mpr
  simpa [stmtVars] using h

theorem stmt_blocks_in_scope {condition : Exp} {body : List Stmt} {x : Bap.Var} {s : Stmt} (hs : s ∈ body)
    (h : x ∈ stmtVars s) : x ∈ (stmtVars (.while condition body)).eraseDups := by
  apply List.mem_eraseDups.mpr
  simp only [stmtVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨s, hs, h⟩

/-- Variables that only differ in type, or in virtuality, render differently side by side. -/
theorem varName_typ_distinct {scope : List Bap.Var} {a b : Bap.Var} (ha : a ∈ scope) (hb : b ∈ scope)
    (hne : a.typ ≠ b.typ ∨ a.isVirtual ≠ b.isVirtual) : varName scope a ≠ varName scope b := by
  intro h
  have := varName_injective_in_scope ha hb h
  subst this
  simp at hne

/-! ### Functions -/

private def paramList (scope params : List Bap.Var) : String :=
  String.intercalate ", " (params.map fun var => s!"{ctype var.typ} {varName scope var}")

private theorem function_eq (name : String) (params : List Bap.Var) (code : Bap.Bil.Program) :
    function name params code =
      "void " ++ identifier name ++ "(" ++ paramList (params ++ code.flatMap stmtVars).eraseDups params ++ ") {" ++
        "\n" ++ bodyIn (params ++ code.flatMap stmtVars).eraseDups code ++ "\n}" :=
  rfl

theorem function_shape (name : String) (params : List Bap.Var) (code : Bap.Bil.Program) :
    ∃ rest, function name params code = "void " ++ identifier name ++ "(" ++ rest :=
  ⟨paramList (params ++ code.flatMap stmtVars).eraseDups params ++ ") {" ++ "\n" ++
      bodyIn (params ++ code.flatMap stmtVars).eraseDups code ++ "\n}", by
    rw [function_eq]; simp only [String.append_assoc]⟩

/-- A function with no parameters and no code. -/
theorem function_empty (name : String) :
    function name [] [] = "void " ++ identifier name ++ "() {\n\n}" := by
  rw [function_eq]
  simp only [paramList, bodyIn, List.map_nil, String.intercalate_nil]
  simp [String.append_assoc]

/-- A whole rendered function has properly nested brackets. -/
theorem function_balanced (name : String) (params : List Bap.Var) {code : Bap.Bil.Program}
    (h : ∀ s ∈ code, StmtBalanced s) : Balanced (function name params code) := by
  have hn := balanced_identifier name
  have hp : ∀ scope, Balanced (paramList scope params) := by
    intro scope
    apply balanced_intercalate (by intro stack; simp [scan])
    intro item hm
    obtain ⟨var, _, rfl⟩ := List.mem_map.mp hm
    have ht := balanced_ctype var.typ
    have hv := balanced_varName scope var
    intro stack
    simp [toString_string, String.toList_append, scan_append, scan, ht _, hv _]
  have hb := bodyIn_balanced (params ++ code.flatMap stmtVars).eraseDups h
  have hp := hp (params ++ code.flatMap stmtVars).eraseDups
  rw [function_eq]
  generalize paramList _ params = P at hp
  generalize bodyIn _ code = B at hb
  intro stack
  simp [String.toList_append, scan_append, scan, hn _, hp _, hb _]

/-! ### Rendering whole projects -/

theorem mem_usedStmt_move (x var : Bap.Var) (value : Exp) :
    x ∈ usedStmt (.move var value) ↔ x ∈ Bap.Bil.freeVars value := by
  simp [usedStmt]

theorem mem_usedStmt_while (x : Bap.Var) (condition : Exp) (body : List Stmt) :
    x ∈ usedStmt (.while condition body) ↔
      x ∈ Bap.Bil.freeVars condition ∨ ∃ s ∈ body, x ∈ usedStmt s := by
  simp [usedStmt]

theorem mem_usedStmt_ifElse (x : Bap.Var) (condition : Exp) (yes no : List Stmt) :
    x ∈ usedStmt (.ifElse condition yes no) ↔
      x ∈ Bap.Bil.freeVars condition ∨ (∃ s ∈ yes, x ∈ usedStmt s) ∨ ∃ s ∈ no, x ∈ usedStmt s := by
  simp [usedStmt]

theorem mem_usedInsns (x : Bap.Var) (instructions : List Bap.Disasm.Insn) :
    x ∈ usedInsns instructions ↔ ∃ insn ∈ instructions, ∃ s ∈ insn.bil, x ∈ usedStmt s := by
  simp [usedInsns]

private theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.Nodup := by
  generalize hn : values.length = n
  induction n using Nat.strongRecOn generalizing values with
  | _ n ih =>
    cases values with
    | nil => simp
    | cons head tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, ih _ ?_ _ rfl⟩
      · simp [List.mem_eraseDups]
      · have := List.length_filter_le (fun x => !x == head) tail
        simp at hn
        omega

theorem usedInsns_nodup (instructions : List Bap.Disasm.Insn) : (usedInsns instructions).Nodup :=
  nodup_eraseDups _

/-- Rendering the project function by function: the parameters are ABI arguments in ABI order
which the owned instructions read, and the body is exactly the owned instructions' BIL. -/
theorem functionDisasm_eq (p : Bap.Project.Project) (symbol : Bap.Image.Symbol) :
    let index := Bap.Analysis.Xrefs.create p
    let owned := (p.disasm.map fun disasm => disasm.instructions.filter fun insn =>
      Bap.Analysis.Xrefs.owns index symbol insn.address).getD []
    ∃ params, functionDisasm p symbol = function symbol.name params (owned.flatMap Bap.Disasm.Insn.bil) ∧
      ∀ x ∈ params, x ∈ usedInsns owned := by
  intro index owned
  unfold functionDisasm
  simp only
  split
  · exact ⟨_, rfl, fun x hx => by simpa using (List.mem_filter.mp hx).2⟩
  · exact ⟨[], rfl, by simp⟩

theorem functionDisasm_no_disasm (p : Bap.Project.Project) (symbol : Bap.Image.Symbol)
    (h : p.disasm = none) : functionDisasm p symbol = function symbol.name [] [] := by
  unfold functionDisasm
  simp only [h, Option.map_none, Option.getD_none]
  split
  · simp only [usedInsns, List.flatMap_nil, List.eraseDups_nil]
    rw [List.filter_eq_nil_iff.mpr (by simp)]
  · simp

theorem project_no_image (p : Bap.Project.Project) (h : p.image = none) : project p = "" := by
  simp [project, h]

theorem project_eq (p : Bap.Project.Project) (image : Bap.Image.Image) (h : p.image = some image) :
    project p = String.intercalate "\n\n"
      ((image.symbols.filter Bap.Image.Symbol.isFunction).map (functionDisasm p)) := by
  simp [project, h]

/-- A project renders with properly nested brackets when all its instructions do. -/
theorem project_balanced (p : Bap.Project.Project)
    (h : ∀ disasm, p.disasm = some disasm → ∀ insn ∈ disasm.instructions, ∀ s ∈ insn.bil, StmtBalanced s) :
    Balanced (project p) := by
  have one : ∀ symbol, Balanced (functionDisasm p symbol) := by
    intro symbol
    obtain ⟨params, e, _⟩ := functionDisasm_eq p symbol
    rw [e]
    apply function_balanced
    intro s hs
    obtain ⟨insn, hi, hs⟩ := List.mem_flatMap.mp hs
    cases hd : p.disasm with
    | none => simp [hd] at hi
    | some disasm =>
      simp [hd] at hi
      exact h disasm hd insn hi.1 s hs
  unfold project
  cases hi : p.image with
  | none => simp; intro stack; simp [scan]
  | some image =>
    simp only [Option.map_some, Option.getD_some]
    apply balanced_intercalate (by intro stack; simp [scan])
    intro item hm
    obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp hm
    exact one symbol

/-! ### Aliases -/

theorem owns_congr_of_alias (index : Bap.Analysis.Xrefs.Index) {a b : Bap.Image.Symbol} (address : Nat)
    (haddr : a.addr = b.addr) (hspan : spans a (nearestStart index address) address =
      spans b (nearestStart index address) address) :
    Bap.Analysis.Xrefs.owns index a address = Bap.Analysis.Xrefs.owns index b address := by
  simp [Bap.Analysis.Xrefs.owns, hspan, haddr]

/-- Aliases own what the function at their address owns, whichever one `functionOf` returned. -/
theorem owns_alias (index : Bap.Analysis.Xrefs.Index) {owner alias : Bap.Image.Symbol} {address : Nat}
    (hf : Bap.Analysis.Xrefs.functionOf index address = some owner) (haddr : alias.addr = owner.addr)
    (hspan : spans alias (nearestStart index address) address = true) :
    Bap.Analysis.Xrefs.owns index alias address = true := by
  simp [Bap.Analysis.Xrefs.owns, hf, hspan, haddr]

private def owned (p : Bap.Project.Project) (symbol : Bap.Image.Symbol) : List Bap.Disasm.Insn :=
  (p.disasm.map fun disasm => disasm.instructions.filter fun insn =>
    Bap.Analysis.Xrefs.owns (Bap.Analysis.Xrefs.create p) symbol insn.address).getD []

/-- Aliases of equal extent own the same instructions, so each renders the same body. -/
theorem functionDisasm_aliases_same_body (p : Bap.Project.Project) {a b : Bap.Image.Symbol}
    (haddr : a.addr = b.addr) (hsize : a.size = b.size) :
    ∃ code paramsA paramsB,
      functionDisasm p a = function a.name paramsA code ∧
      functionDisasm p b = function b.name paramsB code ∧
      code = ((p.disasm.map fun disasm => disasm.instructions.filter fun insn =>
        Bap.Analysis.Xrefs.owns (Bap.Analysis.Xrefs.create p) a insn.address).getD []).flatMap
          Bap.Disasm.Insn.bil := by
  have same : owned p a = owned p b := by
    simp only [owned]
    cases p.disasm with
    | none => rfl
    | some disasm =>
      simp only [Option.map_some, Option.getD_some]
      apply List.filter_congr
      intro insn _
      exact owns_congr_of_alias _ _ haddr (by simp [spans, haddr, hsize])
  obtain ⟨paramsA, ea, _⟩ := functionDisasm_eq p a
  obtain ⟨paramsB, eb, _⟩ := functionDisasm_eq p b
  refine ⟨_, paramsA, paramsB, ea, ?_, rfl⟩
  rw [eb]
  have : ((p.disasm.map fun disasm => disasm.instructions.filter fun insn =>
      Bap.Analysis.Xrefs.owns (Bap.Analysis.Xrefs.create p) b insn.address).getD []) =
      ((p.disasm.map fun disasm => disasm.instructions.filter fun insn =>
      Bap.Analysis.Xrefs.owns (Bap.Analysis.Xrefs.create p) a insn.address).getD []) := same.symm
  rw [this]

/-- An instruction `functionOf` attributes to a function is in the body of every alias spanning it. -/
theorem functionDisasm_alias_owns (p : Bap.Project.Project) {disasm : Bap.Disasm.Disasm}
    (hd : p.disasm = some disasm) {insn : Bap.Disasm.Insn} (hi : insn ∈ disasm.instructions)
    {owner alias : Bap.Image.Symbol}
    (hf : Bap.Analysis.Xrefs.functionOf (Bap.Analysis.Xrefs.create p) insn.address = some owner)
    (haddr : alias.addr = owner.addr)
    (hspan : spans alias (nearestStart (Bap.Analysis.Xrefs.create p) insn.address) insn.address = true) :
    insn ∈ owned p alias := by
  simp only [owned, hd, Option.map_some, Option.getD_some]
  exact List.mem_filter.mpr ⟨hi, owns_alias _ hf haddr hspan⟩

/-! ### What the renderer keeps -/

private def opName (op : BinOp) : String := (signedBinName op).getD (binName op)

/-- The rendered name of an operator determines it, signed and unsigned ones included. -/
theorem opName_injective {a b : BinOp} (h : opName a = opName b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; simp [opName, signedBinName, binName])

theorem signedBinName_injective {a b : BinOp} {name : String} (ha : signedBinName a = some name)
    (hb : signedBinName b = some name) : a = b :=
  opName_injective (by simp [opName, ha, hb])

theorem binName_injective {a b : BinOp} (ha : signedBinName a = none) (hb : signedBinName b = none)
    (h : binName a = binName b) : a = b :=
  opName_injective (by simp [opName, ha, hb, h])

/-- The infix table `binName` covers exactly the operators `signedBinName` leaves out. -/
theorem signedBinName_none_iff (op : BinOp) : signedBinName op = none ↔ binName op ≠ "" := by
  cases op <;> simp [signedBinName, binName]

private theorem signedBinName_no_paren {op : BinOp} {name : String} (h : signedBinName op = some name) :
    '(' ∉ name.toList ∧ name.toList ≠ [] := by
  cases op <;> simp [signedBinName] at h <;> subst h <;> simp

/-- A binary operation's rendering determines its operator: `slt` is not `<`. -/
theorem expIn_bin_op_injective (scope : List Bap.Var) (left right : Exp) {a b : BinOp}
    (hw : leftNeedsWidth a right = leftNeedsWidth b right)
    (h : expIn scope (.bin a left right) = expIn scope (.bin b left right)) : a = b := by
  have hl := congrArg String.toList h
  simp only [expIn] at hl
  have hsame : leftOperand b left right (expIn scope left) = leftOperand a left right (expIn scope left) := by
    simp only [leftOperand, hw]
  rw [hsame] at hl
  generalize leftOperand a left right (expIn scope left) = shown at hl
  apply opName_injective
  cases ha : signedBinName a with
  | some na =>
    cases hb : signedBinName b with
    | some nb =>
      simp only [ha, hb, toString_string, String.toList_append, List.append_assoc] at hl
      have e : na.toList = nb.toList := by simpa using hl
      simp [opName, ha, hb, String.toList_inj.mp e]
    | none =>
      exfalso
      simp only [ha, hb, toString_string, String.toList_append, List.append_assoc] at hl
      have hn := signedBinName_no_paren ha
      cases hna : na.toList with
      | nil => exact hn.2 hna
      | cons c tail =>
        simp [hna] at hl
        exact hn.1 (by simp [hna, hl.1])
  | none =>
    cases hb : signedBinName b with
    | some nb =>
      exfalso
      simp only [ha, hb, toString_string, String.toList_append, List.append_assoc] at hl
      have hn := signedBinName_no_paren hb
      cases hnb : nb.toList with
      | nil => exact hn.2 hnb
      | cons c tail =>
        simp [hnb] at hl
        exact hn.1 (by simp [hnb, ← hl.1])
    | none =>
      simp only [ha, hb, toString_string, String.toList_append, List.append_assoc] at hl
      have e : (binName a).toList = (binName b).toList := by simpa using hl
      simp [opName, ha, hb, String.toList_inj.mp e]

theorem exp_bin_op_injective (left right : Exp) {a b : BinOp}
    (hw : leftNeedsWidth a right = leftNeedsWidth b right)
    (h : exp (.bin a left right) = exp (.bin b left right)) : a = b :=
  expIn_bin_op_injective _ left right hw h

/-- Signed comparisons render distinctly from their unsigned twins. -/
theorem exp_signed_distinct (left right : Exp) {signed unsigned : BinOp}
    (h : (signed, unsigned) ∈ [(BinOp.slt, BinOp.lt), (.sle, .le), (.sgt, .gt), (.sge, .ge)]) :
    exp (.bin signed left right) ≠ exp (.bin unsigned left right) := by
  intro e
  have hw : leftNeedsWidth signed right = leftNeedsWidth unsigned right := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (cases right <;> rfl)
  have := exp_bin_op_injective left right hw e
  subst this
  simp at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (rw [h1] at h2; cases h2)

theorem exp_slt (scope : List Bap.Var) (left right : Exp) :
    expIn scope (.bin .slt left right) =
      "slt(" ++ leftOperand .slt left right (expIn scope left) ++ ", " ++ expIn scope right ++ ")" := by
  simp [expIn, signedBinName, toString_string, String.append_assoc]

/-- A literal on its own says nothing of its width: it takes its type from the context, and the operand widths of a
well-typed expression agree. Where nothing else tells the width, `expIn_tells_width` says it is written. -/
theorem exp_int_forgets_width (n w w' : Nat) (h : n < 2 ^ w) (h' : n < 2 ^ w') :
    exp (.int (BitVec.ofNat w n)) = exp (.int (BitVec.ofNat w' n)) := by
  simp [exp, expIn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h']

private theorem bitInt_toList (w : Nat) :
    (s!"unsigned _BitInt({w})").toList = "unsigned _BitInt(".toList ++ (toString w).toList ++ [')'] := by
  simp [toString_string, String.toList_append]

private theorem bitInt_ne {w : Nat} {fixed : String} (h : (fixed.toList.take 2) ≠ ['u', 'n']) :
    s!"unsigned _BitInt({w})" ≠ fixed := by
  intro e
  have := congrArg (fun s : String => s.toList.take 2) e
  simp only [bitInt_toList] at this
  exact h (by rw [← this]; rfl)

private theorem toString_nat_injective {a b : Nat} (h : toString a = toString b) : a = b := by
  have ha : (toString a).toList = Nat.toDigits 10 a := by rw [Nat.toString_eq_ofList_toDigits]; simp
  have hb : (toString b).toList = Nat.toDigits 10 b := by rw [Nat.toString_eq_ofList_toDigits]; simp
  have e : Nat.toDigits 10 a = Nat.toDigits 10 b := by rw [← ha, ← hb, h]
  have := congrArg (Nat.ofDigitChars 10 · 0) e
  simpa [Nat.ofDigitChars_ten_toDigits] using this

/-- The widths are different types. -/
theorem ctype_imm_injective {a b : Nat} (h : ctype (.imm a) = ctype (.imm b)) : a = b := by
  have hb8 : ∀ {w}, s!"unsigned _BitInt({w})" ≠ "uint8_t" := bitInt_ne (by decide)
  have hb16 : ∀ {w}, s!"unsigned _BitInt({w})" ≠ "uint16_t" := bitInt_ne (by decide)
  have hb32 : ∀ {w}, s!"unsigned _BitInt({w})" ≠ "uint32_t" := bitInt_ne (by decide)
  have hb64 : ∀ {w}, s!"unsigned _BitInt({w})" ≠ "uint64_t" := bitInt_ne (by decide)
  have spec : ∀ w, ctype (.imm w) = if w = 8 then "uint8_t" else if w = 16 then "uint16_t" else if w = 32 then "uint32_t"
      else if w = 64 then "uint64_t" else s!"unsigned _BitInt({w})" := by
    intro w
    unfold ctype
    split <;> simp_all
  rw [spec, spec] at h
  repeat' split at h
  all_goals first
    | omega
    | exact absurd h (by decide)
    | exact absurd h hb8
    | exact absurd h hb16
    | exact absurd h hb32
    | exact absurd h hb64
    | exact absurd h.symm hb8
    | exact absurd h.symm hb16
    | exact absurd h.symm hb32
    | exact absurd h.symm hb64
    | skip
  have e : "unsigned _BitInt(".toList ++ (toString a).toList ++ [')'] =
      "unsigned _BitInt(".toList ++ (toString b).toList ++ [')'] := by
    rw [← bitInt_toList, ← bitInt_toList, h]
  have e2 := List.append_cancel_left (List.append_cancel_right e)
  exact toString_nat_injective (String.toList_inj.mp e2)

/-- Where nothing else tells the width of a literal, its rendering does: under an operator or a cast, in an `extract` or a
`concat`, and to the left of a shift or of another literal. A complement of the zero of 8 bits is not that of 16. -/
theorem withWidth_literal (width : Nat) (value : BitVec width) (rendered : String) :
    withWidth (.int value) rendered = "(" ++ (ctype (.imm width) ++ (")" ++ rendered)) := by
  simp [withWidth, toString_string, String.append_assoc]

/-- A complement shows the width of its literal. -/
theorem expIn_not_literal (scope : List Bap.Var) (width : Nat) (value : BitVec width) :
    expIn scope (.un .not (.int value)) =
      "(~" ++ ("(" ++ (ctype (.imm width) ++ (")" ++ ("0x" ++ (hex value.toNat ++ ")"))))) := by
  simp [expIn, withWidth, unName, toString_string, String.append_assoc]

/-- The left of a shift shows the width of its literal, as nothing on the right tells it. -/
theorem expIn_shift_literal (scope : List Bap.Var) (width : Nat) (value : BitVec width) (right : Exp) :
    expIn scope (.bin .lshift (.int value) right) =
      "(" ++ ("(" ++ (ctype (.imm width) ++ (")" ++ ("0x" ++ (hex value.toNat ++ (" << " ++ (expIn scope right ++ ")"))))))) := by
  have hw : leftNeedsWidth .lshift right = true := by cases right <;> rfl
  simp [expIn, leftOperand, hw, withWidth, signedBinName, binName, toString_string, String.append_assoc]

/-- A name the output uses for itself, its types and its operations included, is not left to mean something else. -/
theorem identifier_reserved {name : String} (h : name ∈ keywords) : identifier name ≠ name :=
  fun e => identifier_not_keyword name (by rw [e]; exact h)

/-- These are some of those names. -/
theorem reserved_names : ["uint8_t", "uint16_t", "uint32_t", "uint64_t", "read32_le", "write8_be", "concat", "extract", "slt",
    "low", "high", "unknown", "special"].all keywords.contains = true := by
  decide +kernel

/-- An unknown value renders with its type. -/
theorem exp_unknown (message : String) (typ : Bap.Typ) :
    exp (.unknown message typ) = "unknown(" ++ quote message ++ ", " ++ ctype typ ++ ")" := by
  simp [exp, expIn, toString_string, String.append_assoc]

/-- A store to the memory it reads renders as a bare write. -/
theorem stmt_store_in_place (scope : List Bap.Var) (level : Nat) (var : Bap.Var) (address value : Exp)
    (endian : Bap.Endian) (size : Nat) :
    stmtIn scope level (.move var (.store (.var var) address value endian size)) =
      indentation level ++ writeText scope (.var var) address value endian size := by
  rw [stmt_store_eq]; simp [inPlace]

/-- Any other store names its destination. -/
theorem stmt_store_other_memory (scope : List Bap.Var) (level : Nat) (var : Bap.Var) (memory address value : Exp)
    (endian : Bap.Endian) (size : Nat) (h : ∀ source, memory = .var source → source ≠ var) :
    stmtIn scope level (.move var (.store memory address value endian size)) =
      indentation level ++ varName scope var ++ " = " ++ writeText scope memory address value endian size := by
  rw [stmt_store_eq]
  have : inPlace var memory = false := by
    cases memory <;> simp [inPlace]
    exact h _ rfl
  simp [this]

/-- The destination of a store can be read back from its rendering. -/
theorem stmt_store_destination {scope : List Bap.Var} (level : Nat) {var var' : Bap.Var}
    (hv : var ∈ scope) (hv' : var' ∈ scope) (memory address value : Exp)
    (endian : Bap.Endian) (size : Nat)
    (h : stmtIn scope level (.move var (.store memory address value endian size)) =
      stmtIn scope level (.move var' (.store memory address value endian size))) :
    var = var' := by
  simp only [stmt_store_eq] at h
  have longer : ∀ (v : Bap.Var) (w : String), ¬ w = varName scope v ++ " = " ++ w := by
    intro v w e
    have := congrArg String.length e
    simp at this
  generalize writeText scope memory address value endian size = w at h
  cases hp : inPlace var memory <;> cases hp' : inPlace var' memory <;> simp only [hp, hp', Bool.false_eq_true, ↓reduceIte] at h
  · have hl := congrArg String.toList h
    simp only [String.toList_append, List.append_assoc, List.append_cancel_left_eq] at hl
    have e : (varName scope var).toList = (varName scope var').toList := by simpa using hl
    exact varName_injective_in_scope hv hv' (String.toList_inj.mp e)
  · exfalso
    have e : varName scope var ++ " = " ++ w = w := by
      have hl := congrArg String.toList h
      apply String.toList_inj.mp
      simpa [String.toList_append, List.append_assoc] using hl
    exact longer var w e.symm
  · exfalso
    have e : w = varName scope var' ++ " = " ++ w := by
      have hl := congrArg String.toList h
      apply String.toList_inj.mp
      simpa [String.toList_append, List.append_assoc] using hl
    exact longer var' w e
  · cases memory <;> simp [inPlace] at hp hp'
    rw [← hp, hp']

/-- A direct jump renders as a `goto` to its label. -/
theorem stmt_jmp_direct {width : Nat} (scope : List Bap.Var) (level : Nat) (target : BitVec width) :
    stmtIn scope level (.jmp (.int target)) = indentation level ++ "goto loc_" ++ hex target.toNat ++ ";" := by
  simp [toString_string, stmtIn]

/-- A computed jump renders as a computed `goto`, not as a `return`. -/
theorem stmt_jmp_computed (scope : List Bap.Var) (level : Nat) (target : Exp)
    (h : match target with | .int _ => False | _ => True) :
    stmtIn scope level (.jmp target) = indentation level ++ "goto *" ++ expIn scope target ++ ";" := by
  cases target <;> first | exact h.elim | simp [toString_string, stmtIn]

theorem ctype_standard :
    ctype (.imm 8) = "uint8_t" ∧ ctype (.imm 16) = "uint16_t" ∧
      ctype (.imm 32) = "uint32_t" ∧ ctype (.imm 64) = "uint64_t" := by
  simp [ctype]

/-- Other integer widths keep their width instead of rendering as `uint64_t`. -/
theorem ctype_other (width : Nat) (h : width ≠ 8 ∧ width ≠ 16 ∧ width ≠ 32 ∧ width ≠ 64) :
    ctype (.imm width) = "unsigned _BitInt(" ++ toString width ++ ")" := by
  obtain ⟨h8, h16, h32, h64⟩ := h
  unfold ctype
  split <;> simp_all [toString_string, String.append_assoc]

end Bap.Proofs.Decompile
