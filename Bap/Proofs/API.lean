import Lean.Elab.Tactic.Basic
import Bap.API

namespace Bap.Proofs.API

open Bap.API Bap.ABI

open Lean Elab Term in
/-- Names a private constant of another module: `priv% Module Full.Name`. -/
local elab "priv% " mod:ident n:ident : term => do
  return mkConst (mkPrivateNameCore mod.getId n.getId)

open Lean Elab Tactic in
/-- `unfold` for a private definition of another module. -/
local elab "punfold " mod:ident n:ident " at " h:ident : tactic => do
  evalTactic (← `(tactic| unfold $(mkIdent (mkPrivateNameCore mod.getId n.getId)):ident at $h:ident))

open Lean Elab Tactic in
/-- Rewrites with the unfolding equation of a private definition of another module. -/
local elab "prw " mod:ident n:ident : tactic => do
  evalTactic (← `(tactic| rw [$(mkIdent (mkPrivateNameCore mod.getId (n.getId ++ `eq_def))):ident]))

private abbrev trim : String → String := priv% Bap.API Bap.API.trim
private abbrev words : String → List String := priv% Bap.API Bap.API.words
private abbrev identChar : Char → Bool := priv% Bap.API Bap.API.identChar
private abbrev pointers : Nat → CType → CType := priv% Bap.API Bap.API.pointers
private abbrev parseType : String → Except String CType := priv% Bap.API Bap.API.parseType
private abbrev parseParameter : String → Except String Parameter :=
  priv% Bap.API Bap.API.parseParameter
private abbrev parseParameters : String → Except String (List Parameter × Bool) :=
  priv% Bap.API Bap.API.parseParameters
private abbrev stripLineComment : List Char → List Char := priv% Bap.API Bap.API.stripLineComment
private abbrev stripBlockComment : List Char → List Char := priv% Bap.API Bap.API.stripBlockComment
private abbrev stripCommentsAux : Nat → List Char → List Char := priv% Bap.API Bap.API.stripCommentsAux
private abbrev stripComments : List Char → List Char := priv% Bap.API Bap.API.stripComments

/-! ## Argument locations -/

private theorem location_stack_iff (abi : Convention) (index : Nat) :
    (∃ offset, argumentLocation abi index = .stack offset) ↔
      abi.functionArguments.length ≤ index := by
  unfold argumentLocation
  cases h : abi.functionArguments[index]? with
  | none => simpa using List.getElem?_eq_none_iff.1 h
  | some var =>
    have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 h
    simp only [reduceCtorEq, exists_false, false_iff]
    omega

theorem argumentLocations_getElem (abi : Convention) (prototype : Prototype) (i : Nat)
    (h : i < prototype.params.length) :
    (argumentLocations abi prototype)[i]'(by simpa [argumentLocations] using h) =
      argumentLocation abi i := by
  simp [argumentLocations]

/-- Locations depend on the number of parameters only, not their names, types or the result. -/
theorem argumentLocations_congr (abi : Convention) (p q : Prototype)
    (h : p.params.length = q.params.length) :
    argumentLocations abi p = argumentLocations abi q := by
  simp [argumentLocations, h]

/-- Appending parameters extends the list of locations without moving earlier ones. -/
theorem argumentLocations_append (abi : Convention) (p : Prototype) (extra : List Parameter) :
    argumentLocations abi { p with params := p.params ++ extra } =
      argumentLocations abi p ++
        (List.range extra.length).map fun i => argumentLocation abi (p.params.length + i) := by
  simp [argumentLocations, List.range_add, List.map_map, Function.comp_def]

/-- Registers fill up first: no register location follows a stack location. -/
theorem argumentLocations_registers_first (abi : Convention) (prototype : Prototype) :
    (argumentLocations abi prototype).Pairwise fun a b =>
      (∃ offset, a = .stack offset) → ∃ offset, b = .stack offset := by
  refine List.pairwise_map.2 (List.Pairwise.imp ?_ List.pairwise_lt_range)
  intro a b hab ha
  have := (location_stack_iff abi a).1 ha
  exact (location_stack_iff abi b).2 (by omega)

/-- Exactly the first `min` parameters are in registers; the rest are on the stack. -/
theorem argumentLocations_stack_count (abi : Convention) (prototype : Prototype) :
    ((argumentLocations abi prototype).filter fun location =>
        match location with
        | .stack _ => true
        | .register _ => false).length =
      prototype.params.length - abi.functionArguments.length := by
  unfold argumentLocations
  generalize prototype.params.length = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append, ih]
    by_cases h : abi.functionArguments.length ≤ n
    · have ⟨offset, ho⟩ := (location_stack_iff abi n).2 h
      simp [ho]
      omega
    · have hn : ¬∃ offset, argumentLocation abi n = .stack offset :=
        fun hx => h ((location_stack_iff abi n).1 hx)
      cases hl : argumentLocation abi n with
      | stack offset => exact absurd ⟨offset, hl⟩ hn
      | register var =>
        simp [hl]
        omega

/-- With distinct registers and non-empty words no two parameters share a location. -/
theorem argumentLocations_nodup (abi : Convention) (prototype : Prototype)
    (hn : abi.functionArguments.Nodup) (hw : 8 ≤ abi.wordSize) :
    (argumentLocations abi prototype).Nodup := by
  have hinj : ∀ i j, i < j → argumentLocation abi i ≠ argumentLocation abi j := by
    intro i j hij he
    have hbyte : 0 < abi.wordSize / 8 := Nat.div_pos hw (by omega)
    unfold argumentLocation at he
    cases hi : abi.functionArguments[i]? with
    | none =>
      have hge := List.getElem?_eq_none_iff.1 hi
      have hj : abi.functionArguments[j]? = none := List.getElem?_eq_none_iff.2 (by omega)
      rw [hi, hj] at he
      have := Nat.eq_of_mul_eq_mul_right hbyte (Nat.add_left_cancel (Location.stack.inj he))
      omega
    | some a =>
      cases hj : abi.functionArguments[j]? with
      | none => rw [hi, hj] at he; cases he
      | some b =>
        rw [hi, hj] at he
        have heq := Location.register.inj he
        have ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hi
        have ⟨h3, h4⟩ := List.getElem?_eq_some_iff.1 hj
        exact List.pairwise_iff_getElem.1 hn i j h1 h3 hij (by rw [h2, h4, heq])
  refine List.pairwise_map.2 (List.Pairwise.imp ?_ List.pairwise_lt_range)
  intro a b hab
  exact hinj a b hab

/-! ## C types -/

/-- Number of pointer levels. -/
def depth : CType → Nat
  | .named _ => 0
  | .pointer type => depth type + 1

/-- The named type under all pointer levels. -/
def base : CType → String
  | .named name => name
  | .pointer type => base type

private theorem pointers_zero (type : CType) : pointers 0 type = type := rfl

private theorem pointers_succ (count : Nat) (type : CType) :
    pointers (count + 1) type = .pointer (pointers count type) := rfl

theorem depth_pointers (count : Nat) (type : CType) :
    depth (pointers count type) = count + depth type := by
  induction count with
  | zero => rw [pointers_zero]; omega
  | succ n ih => rw [pointers_succ]; simp only [depth, ih]; omega

theorem base_pointers (count : Nat) (type : CType) :
    base (pointers count type) = base type := by
  induction count with
  | zero => rw [pointers_zero]
  | succ n ih => rw [pointers_succ]; simpa only [base] using ih

theorem pointers_add (m n : Nat) (type : CType) :
    pointers (m + n) type = pointers m (pointers n type) := by
  induction m with
  | zero => rw [Nat.zero_add, pointers_zero]
  | succ m ih => rw [Nat.add_right_comm, pointers_succ, pointers_succ, ih]

/-- Normal form: every C type is its base name under `depth` pointer levels. -/
theorem pointers_normal_form (type : CType) :
    pointers (depth type) (.named (base type)) = type := by
  induction type with
  | named name => rfl
  | pointer type ih =>
    simp only [depth, base]
    rw [pointers_succ, ih]

/-- `pointers` over a named base is injective in both arguments. -/
theorem pointers_named_inj (m n : Nat) (a b : String) :
    pointers m (.named a) = pointers n (.named b) ↔ m = n ∧ a = b := by
  constructor
  · intro h
    have hd := congrArg depth h
    have hb := congrArg base h
    simp only [depth_pointers, base_pointers, depth, base] at hd hb
    exact ⟨by omega, hb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## `parseType` -/

/-- The base name `parseType` extracts. -/
def baseOf (input : String) : String :=
  trim (String.ofList (input.toList.filter (· != '*')))

private theorem parseType_eq (input : String) :
    parseType input =
      if (baseOf input).isEmpty then .error "C type has no base name"
      else .ok (pointers (input.toList.count '*') (.named (baseOf input))) := rfl

theorem parseType_ok_iff (input : String) (type : CType) :
    parseType input = .ok type ↔
      (baseOf input).isEmpty = false ∧
        type = pointers (input.toList.count '*') (.named (baseOf input)) := by
  rw [parseType_eq]
  cases h : (baseOf input).isEmpty <;> simp [eq_comm]

theorem parseType_error_iff (input : String) (error : String) :
    parseType input = .error error ↔
      (baseOf input).isEmpty = true ∧ error = "C type has no base name" := by
  rw [parseType_eq]
  cases h : (baseOf input).isEmpty <;> simp [eq_comm]

/-- Pointer depth of a parsed type counts the stars of the input, and the base is non-empty. -/
theorem parseType_shape (input : String) (type : CType) (h : parseType input = .ok type) :
    depth type = input.toList.count '*' ∧ base type = baseOf input ∧ (base type).isEmpty = false := by
  have ⟨h1, h2⟩ := (parseType_ok_iff input type).1 h
  subst h2
  simp only [depth_pointers, base_pointers, depth, base, Nat.add_zero, true_and]
  exact h1

/-- Algebraic law: one more star anywhere in a type adds exactly one pointer level. -/
theorem parseType_insert_star (before after : List Char) :
    parseType (String.ofList (before ++ '*' :: after)) =
      (parseType (String.ofList (before ++ after))).map CType.pointer := by
  have hbase : baseOf (String.ofList (before ++ '*' :: after)) =
      baseOf (String.ofList (before ++ after)) := by
    simp [baseOf, List.filter_append]
  rw [parseType_eq, parseType_eq, hbase]
  cases h : (baseOf (String.ofList (before ++ after))).isEmpty with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false, Except.map, String.toList_ofList]
    have : (before ++ '*' :: after).count '*' = (before ++ after).count '*' + 1 := by
      simp [List.count_append]
      omega
    rw [this, pointers_succ]

/-! ## Well-formedness of parse results -/

/-- A parsed parameter: non-empty base type; name absent or a non-empty identifier. -/
def ParameterOk (p : Parameter) : Prop :=
  (base p.typ).isEmpty = false ∧ (p.name = "" ∨ (p.name.isEmpty = false ∧ p.name.all identChar = true))

/-- A parsed prototype: identifier name, non-empty result type, well-formed parameters. -/
def PrototypeOk (p : Prototype) : Prop :=
  p.name.isEmpty = false ∧ p.name.all identChar = true ∧ (base p.result).isEmpty = false ∧
    ∀ q ∈ p.params, ParameterOk q

private theorem except_bind_ok {α β ε} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem mem_words_nonempty (input word : String) (h : word ∈ words input) :
    word.isEmpty = false := by
  have h' : word ∈ ((trim input).splitOn " ").filter fun word => !word.isEmpty := h
  simpa using (List.mem_filter.1 h').2

private theorem parameter_of_parseType (input name : String) (p : Parameter)
    (hn : name = "" ∨ (name.isEmpty = false ∧ name.all identChar = true))
    (h : (do let t ← parseType input; Except.ok { name := name, typ := t }) =
      (Except.ok p : Except String Parameter)) : ParameterOk p := by
  have ⟨t, ht, hp⟩ := except_bind_ok h
  cases hp
  exact ⟨(parseType_shape input t ht).2.2, hn⟩

theorem parseParameter_ok (input : String) (p : Parameter) (h : parseParameter input = .ok p) :
    ParameterOk p := by
  dsimp only [parseParameter] at h
  punfold Bap.API Bap.API.parseParameter at h
  simp only [] at h
  split at h
  · cases h
  · rename_i single hw
    split at h
    · cases h
      refine ⟨?_, .inl rfl⟩
      have hw' : words input = [single] := hw
      exact mem_words_nonempty input single (by rw [hw']; simp)
    · exact parameter_of_parseType _ _ _ (.inl rfl) h
  · split at h
    · rename_i hc
      have hc' := Bool.and_eq_true_iff.1 hc
      exact parameter_of_parseType _ _ _
        (.inr ⟨by simpa using hc'.1, hc'.2⟩) h
    · exact parameter_of_parseType _ _ _ (.inl rfl) h

private theorem mapM_ok {α β ε} {f : α → Except ε β} {l : List α} {r : List β}
    (h : l.mapM f = .ok r) : r.length = l.length ∧ ∀ y ∈ r, ∃ x ∈ l, f x = .ok y := by
  induction l generalizing r with
  | nil =>
    rw [List.mapM_nil] at h
    cases h
    simp
  | cons a l ih =>
    rw [List.mapM_cons] at h
    have ⟨y, hy, h1⟩ := except_bind_ok h
    have ⟨ys, hys, h2⟩ := except_bind_ok h1
    cases h2
    have ⟨hlen, hmem⟩ := ih hys
    refine ⟨by simp [hlen], ?_⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨a, by simp, hy⟩
    · have ⟨x, hx, hf⟩ := hmem z hz
      exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩

private theorem mapM_error {α β ε} {f : α → Except ε β} {l : List α} {a : α} {e : ε}
    (hm : a ∈ l) (he : f a = .error e) : ∃ e', l.mapM f = (.error e' : Except ε (List β)) := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    rw [List.mapM_cons]
    cases hx : f x with
    | error e' => exact ⟨e', rfl⟩
    | ok y =>
      rcases List.mem_cons.1 hm with rfl | hm'
      · rw [he] at hx
        cases hx
      · have ⟨e', he'⟩ := ih hm'
        exact ⟨e', by simp [he', bind, Except.bind]⟩

/-- The comma-separated pieces of a parameter list. -/
def parameterParts (input : String) : List String :=
  ((trim input).splitOn "," |>.map trim).filter fun part => !part.isEmpty

theorem parseParameters_blank (input : String) (h : (trim input).isEmpty = true) :
    parseParameters input = .ok ([], false) := by
  have : ((trim input).isEmpty || decide (trim input = "void")) = true := by simp [h]
  show (if ((trim input).isEmpty || decide (trim input = "void")) = true then _ else _) = _
  rw [ite_eq_left this]

theorem parseParameters_void (input : String) (h : trim input = "void") :
    parseParameters input = .ok ([], false) := by
  have : ((trim input).isEmpty || decide (trim input = "void")) = true := by simp [h]
  show (if ((trim input).isEmpty || decide (trim input = "void")) = true then _ else _) = _
  rw [ite_eq_left this]

/-- A non-trivial parameter list: `...` sets the variadic flag and contributes no parameter,
all others contribute exactly one well-formed parameter. -/
theorem parseParameters_ok (input : String) (ps : List Parameter) (variadic : Bool)
    (h : parseParameters input = .ok (ps, variadic)) :
    (∀ p ∈ ps, ParameterOk p) ∧
      (ps = [] ∧ variadic = false ∨
        variadic = (parameterParts input).contains "..." ∧
          ps.length = ((parameterParts input).filter (· != "...")).length) := by
  have heq : parseParameters input =
      if ((trim input).isEmpty || decide (trim input = "void")) = true then .ok ([], false)
      else ((parameterParts input).filter (· != "...")).mapM parseParameter >>= fun params =>
        .ok (params, (parameterParts input).contains "...") := rfl
  rw [heq] at h
  split at h
  · cases h
    exact ⟨by simp, .inl ⟨rfl, rfl⟩⟩
  · have ⟨params, hm, hp⟩ := except_bind_ok h
    cases hp
    have ⟨hlen, hmem⟩ := mapM_ok hm
    refine ⟨?_, .inr ⟨rfl, hlen⟩⟩
    intro p hp
    have ⟨_, _, hx⟩ := hmem p hp
    exact parseParameter_ok _ _ hx

/-- Any prototype parsed from any text is well-formed. -/
theorem parsePrototype_ok (input : String) (p : Prototype) (h : parsePrototype input = .ok p) :
    PrototypeOk p := by
  unfold parsePrototype at h
  simp only [] at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hname
        have ⟨⟨ps, v⟩, hps, h1⟩ := except_bind_ok h
        have ⟨t, ht, h2⟩ := except_bind_ok h1
        cases h2
        have hn : ∀ {a b : Bool}, ¬(a || !b) = true → a = false ∧ b = true := by
          intro a b hab
          cases a <;> cases b <;> simp_all
        have ⟨hn1, hn2⟩ := hn hname
        exact ⟨hn1, hn2, (parseType_shape _ _ ht).2.2, (parseParameters_ok _ _ _ hps).1⟩
  · cases h

/-- Text whose trimmed form does not have exactly one `(` is always rejected. -/
theorem parsePrototype_rejects_paren_count (input : String)
    (h : ((trim input).splitOn "(").length ≠ 2) :
    ∃ error, parsePrototype input = .error error := by
  unfold parsePrototype
  simp only []
  split
  · rename_i signature rest hw
    show ∃ error, _
    exact absurd (by have hw' : (trim input).splitOn "(" = [signature, rest] := hw
                     rw [hw']; rfl) h
  · exact ⟨_, rfl⟩

/-- A header parse succeeds only with well-formed prototypes, each parsed from some declaration. -/
theorem parseHeader_ok (input : String) (ps : List Prototype) (h : parseHeader input = .ok ps) :
    ∀ p ∈ ps, PrototypeOk p ∧ ∃ declaration, parsePrototype declaration = .ok p := by
  unfold parseHeader at h
  simp only [] at h
  intro p hp
  have ⟨_, hmem⟩ := mapM_ok h
  have ⟨d, _, hd⟩ := hmem p hp
  exact ⟨parsePrototype_ok _ _ hd, d, hd⟩

/-- The declarations `parseHeader` hands to `parsePrototype`. -/
def headerDeclarations (input : String) : List String :=
  ((String.ofList (stripComments input.toList)).splitOn ";" |>.map trim).filter fun declaration =>
    !declaration.isEmpty && declaration.contains '(' && !declaration.contains '{'

/-- Header parsing is all-or-nothing: one bad declaration fails the whole header. -/
theorem parseHeader_fails_on_bad_declaration (input declaration error : String)
    (hd : declaration ∈ headerDeclarations input) (he : parsePrototype declaration = .error error) :
    ∃ error', parseHeader input = .error error' :=
  mapM_error hd he

/-- A successful header parse produces one prototype per declaration. -/
theorem parseHeader_length (input : String) (ps : List Prototype)
    (h : parseHeader input = .ok ps) : ps.length = (headerDeclarations input).length :=
  (mapM_ok (l := headerDeclarations input) h).1

/-! ## Comment stripping -/

private theorem line_nil : stripLineComment [] = [] := rfl

private theorem line_newline (rest : List Char) :
    stripLineComment ('\n' :: rest) = '\n' :: rest := rfl

private theorem line_cons (c : Char) (rest : List Char) (h : c ≠ '\n') :
    stripLineComment (c :: rest) = stripLineComment rest := by
  dsimp only [stripLineComment]
  prw Bap.API Bap.API.stripLineComment
  simp

/-- A line comment runs up to, and keeps, the next newline. -/
theorem stripLineComment_eq_dropWhile (input : List Char) :
    stripLineComment input = input.dropWhile (· != '\n') := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : c = '\n'
    · subst h
      rfl
    · rw [line_cons c rest h, ih]
      simp [h]

theorem stripLineComment_suffix (input : List Char) : stripLineComment input <:+ input := by
  rw [stripLineComment_eq_dropWhile]
  exact List.dropWhile_suffix _

private theorem block_cons (c : Char) (rest : List Char)
    (h : ¬(c = '*' ∧ rest.head? = some '/')) :
    stripBlockComment (c :: rest) = stripBlockComment rest := by
  dsimp only [stripBlockComment]
  prw Bap.API Bap.API.stripBlockComment
  split <;> simp_all

theorem stripBlockComment_suffix (input : List Char) : stripBlockComment input <:+ input := by
  induction input with
  | nil => exact List.suffix_refl _
  | cons c rest ih =>
    by_cases h : c = '*' ∧ rest.head? = some '/'
    · obtain ⟨rfl, hh⟩ := h
      cases rest with
      | nil => simp at hh
      | cons d tail =>
        have hd : d = '/' := by simpa using hh
        subst hd
        exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
    · rw [block_cons c rest h]
      exact ih.trans (List.suffix_cons _ _)

private abbrev NoClose (input : List Char) : Prop := ∀ xs ys, input ≠ xs ++ '*' :: '/' :: ys

private theorem NoClose.tail {c : Char} {rest : List Char} (h : NoClose (c :: rest)) :
    NoClose rest := fun xs ys he => h (c :: xs) ys (by simp [he])

/-- A block comment ends at its first terminator. -/
theorem stripBlockComment_first_close (body post : List Char) (h : NoClose body) :
    stripBlockComment (body ++ '*' :: '/' :: post) = post := by
  induction body with
  | nil => rfl
  | cons c rest ih =>
    rw [List.cons_append, block_cons]
    · exact ih h.tail
    · rintro ⟨rfl, hh⟩
      cases rest with
      | nil => simp at hh
      | cons d tail =>
        have hd : d = '/' := by simpa using hh
        subst hd
        exact h [] tail (by simp)

/-- An unterminated block comment swallows the remaining input. -/
theorem stripBlockComment_unterminated (body : List Char) (h : NoClose body) :
    stripBlockComment body = [] := by
  induction body with
  | nil => rfl
  | cons c rest ih =>
    rw [block_cons]
    · exact ih h.tail
    · rintro ⟨rfl, hh⟩
      cases rest with
      | nil => simp at hh
      | cons d tail =>
        have hd : d = '/' := by simpa using hh
        subst hd
        exact h [] tail (by simp)

private theorem aux_nil (fuel : Nat) : stripCommentsAux fuel [] = [] := by
  cases fuel <;> rfl

private theorem aux_block (fuel : Nat) (rest : List Char) :
    stripCommentsAux (fuel + 1) ('/' :: '*' :: rest) =
      ' ' :: stripCommentsAux fuel (stripBlockComment rest) :=
  rfl

private theorem aux_line (fuel : Nat) (rest : List Char) :
    stripCommentsAux (fuel + 1) ('/' :: '/' :: rest) = stripCommentsAux fuel (stripLineComment rest) :=
  rfl

private theorem aux_other (fuel : Nat) (c : Char) (rest : List Char)
    (h : ¬(c = '/' ∧ (rest.head? = some '*' ∨ rest.head? = some '/'))) :
    stripCommentsAux (fuel + 1) (c :: rest) = c :: stripCommentsAux fuel rest := by
  dsimp only [stripCommentsAux]
  prw Bap.API Bap.API.stripCommentsAux
  split <;> (try split) <;> simp_all

/-- Three-way case split on the head of an input. -/
private theorem head_cases (c : Char) (rest : List Char) :
    (∃ tail, c = '/' ∧ rest = '*' :: tail) ∨ (∃ tail, c = '/' ∧ rest = '/' :: tail) ∨
      ¬(c = '/' ∧ (rest.head? = some '*' ∨ rest.head? = some '/')) := by
  by_cases hc : c = '/'
  · cases rest with
    | nil => simp
    | cons d tail =>
      by_cases h1 : d = '*'
      · exact .inl ⟨tail, hc, by simp [h1]⟩
      · by_cases h2 : d = '/'
        · exact .inr (.inl ⟨tail, hc, by simp [h2]⟩)
        · exact .inr (.inr (by simp [h1, h2]))
  · exact .inr (.inr (by simp [hc]))

/-- Fuel independence: any fuel above the input length gives the same result. -/
theorem stripCommentsAux_fuel (f g : Nat) (input : List Char) (hf : input.length < f)
    (hg : input.length < g) : stripCommentsAux f input = stripCommentsAux g input := by
  induction f generalizing g input with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      cases input with
      | nil => rw [aux_nil, aux_nil]
      | cons c rest =>
        simp only [List.length_cons] at hf hg
        rcases head_cases c rest with ⟨tail, rfl, rfl⟩ | ⟨tail, rfl, rfl⟩ | h
        · have := (stripBlockComment_suffix tail).length_le
          simp only [List.length_cons] at hf hg
          rw [aux_block, aux_block, ih g _ (by omega) (by omega)]
        · have := (stripLineComment_suffix tail).length_le
          simp only [List.length_cons] at hf hg
          rw [aux_line, aux_line]
          exact ih g _ (by omega) (by omega)
        · rw [aux_other f c rest h, aux_other g c rest h, ih g rest (by omega) (by omega)]

private theorem strip_eq (input : List Char) :
    stripComments input = stripCommentsAux (input.length + 1) input := rfl

theorem stripComments_nil : stripComments [] = [] := rfl

/-- Recursion equation for a character outside any comment opener. -/
theorem stripComments_other (c : Char) (rest : List Char)
    (h : ¬(c = '/' ∧ (rest.head? = some '*' ∨ rest.head? = some '/'))) :
    stripComments (c :: rest) = c :: stripComments rest := by
  rw [strip_eq, strip_eq, aux_other _ c rest h]
  rfl

/-- A block comment reads as one space, as C prescribes. -/
theorem stripComments_block (rest : List Char) :
    stripComments ('/' :: '*' :: rest) = ' ' :: stripComments (stripBlockComment rest) := by
  have := (stripBlockComment_suffix rest).length_le
  rw [strip_eq, strip_eq, aux_block]
  exact congrArg _ (stripCommentsAux_fuel _ _ _ (by simp only [List.length_cons]; omega) (by omega))

theorem stripComments_line (rest : List Char) :
    stripComments ('/' :: '/' :: rest) = stripComments (stripLineComment rest) := by
  have := (stripLineComment_suffix rest).length_le
  rw [strip_eq, strip_eq, aux_line]
  exact stripCommentsAux_fuel _ _ _ (by simp only [List.length_cons]; omega) (by omega)

theorem stripComments_length_le (input : List Char) :
    (stripComments input).length ≤ input.length := by
  induction h : input.length using Nat.strongRecOn generalizing input with
  | _ n ih =>
    cases input with
    | nil => simp [stripComments_nil]
    | cons c rest =>
      simp only [List.length_cons] at h
      rcases head_cases c rest with ⟨tail, rfl, rfl⟩ | ⟨tail, rfl, rfl⟩ | hc
      · have hs := (stripBlockComment_suffix tail).length_le
        simp only [List.length_cons] at h ⊢
        rw [stripComments_block]
        have := ih _ (by omega) (stripBlockComment tail) rfl
        simp only [List.length_cons]
        omega
      · have hs := (stripLineComment_suffix tail).length_le
        simp only [List.length_cons] at h ⊢
        rw [stripComments_line]
        have := ih _ (by omega) (stripLineComment tail) rfl
        omega
      · rw [stripComments_other c rest hc]
        have := ih _ (by omega) rest rfl
        simp only [List.length_cons]
        omega

/-- Text without a comment opener is unchanged. -/
theorem stripComments_of_no_opener (input : List Char)
    (h1 : ∀ xs ys, input ≠ xs ++ '/' :: '*' :: ys) (h2 : ∀ xs ys, input ≠ xs ++ '/' :: '/' :: ys) :
    stripComments input = input := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
    rw [stripComments_other, ih]
    · exact fun xs ys he => h1 (c :: xs) ys (by simp [he])
    · exact fun xs ys he => h2 (c :: xs) ys (by simp [he])
    · rintro ⟨rfl, hh⟩
      cases rest with
      | nil => simp at hh
      | cons d tail =>
        rcases hh with hh | hh
        · have hd : d = '*' := by simpa using hh
          subst hd
          exact h1 [] tail (by simp)
        · have hd : d = '/' := by simpa using hh
          subst hd
          exact h2 [] tail (by simp)

private theorem strip_pre (pre rest : List Char) (hpre : '/' ∉ pre) :
    stripComments (pre ++ rest) = pre ++ stripComments rest := by
  induction pre with
  | nil => rfl
  | cons c tail ih =>
    have hc : c ≠ '/' := fun he => hpre (by simp [he])
    rw [List.cons_append, stripComments_other c _ (by simp [hc]),
      ih (fun hm => hpre (List.mem_cons_of_mem _ hm))]
    rfl

/-- Removing a terminated block comment after comment-free text leaves a space in its place. -/
theorem stripComments_remove_block (pre body post : List Char) (hpre : '/' ∉ pre)
    (hbody : NoClose body) :
    stripComments (pre ++ '/' :: '*' :: (body ++ '*' :: '/' :: post)) =
      pre ++ ' ' :: stripComments post := by
  rw [strip_pre _ _ hpre, stripComments_block, stripBlockComment_first_close _ _ hbody]

/-- Removing a line comment after comment-free text keeps its newline. -/
theorem stripComments_remove_line (pre body post : List Char) (hpre : '/' ∉ pre)
    (hbody : '\n' ∉ body) :
    stripComments (pre ++ '/' :: '/' :: (body ++ '\n' :: post)) =
      pre ++ '\n' :: stripComments post := by
  have hline : stripLineComment (body ++ '\n' :: post) = '\n' :: post := by
    induction body with
    | nil => rfl
    | cons c rest ih =>
      have hc : c ≠ '\n' := fun he => hbody (by simp [he])
      rw [List.cons_append, line_cons c _ hc, ih (fun hm => hbody (List.mem_cons_of_mem _ hm))]
  rw [strip_pre _ _ hpre, stripComments_line, hline, stripComments_other '\n' post (by simp)]

/-- A comment separates the tokens around it: `int/**/f` reads as `int f`. -/
theorem stripComments_separates_tokens (before after : List Char) (hb : '/' ∉ before) :
    stripComments (before ++ ['/', '*', '*', '/'] ++ after) =
      before ++ ' ' :: stripComments after := by
  have := stripComments_remove_block before [] after hb (by
    intro xs ys he
    cases xs <;> simp at he)
  simpa using this

/-- Soundness of the stripper: no comment opener survives in its output. -/
theorem stripComments_no_opener (input : List Char) :
    (∀ xs ys, stripComments input ≠ xs ++ '/' :: '*' :: ys) ∧
      ∀ xs ys, stripComments input ≠ xs ++ '/' :: '/' :: ys := by
  induction h : input.length using Nat.strongRecOn generalizing input with
  | _ n ih =>
    cases input with
    | nil =>
      rw [stripComments_nil]
      constructor <;> (intro xs ys he; cases xs <;> simp at he)
    | cons c rest =>
      simp only [List.length_cons] at h
      rcases head_cases c rest with ⟨tail, rfl, rfl⟩ | ⟨tail, rfl, rfl⟩ | hc
      · have hs := (stripBlockComment_suffix tail).length_le
        simp only [List.length_cons] at h
        rw [stripComments_block]
        have ⟨h1, h2⟩ := ih _ (by omega) (stripBlockComment tail) rfl
        constructor
        · intro xs ys he
          cases xs with
          | nil => simp at he
          | cons x xs => exact h1 xs ys (List.cons.inj he).2
        · intro xs ys he
          cases xs with
          | nil => simp at he
          | cons x xs => exact h2 xs ys (List.cons.inj he).2
      · have hs := (stripLineComment_suffix tail).length_le
        simp only [List.length_cons] at h
        rw [stripComments_line]
        exact ih _ (by omega) (stripLineComment tail) rfl
      · rw [stripComments_other c rest hc]
        have ⟨h1, h2⟩ := ih _ (by omega) rest rfl
        -- the head of the output on `rest` is the head of `rest` unless `rest` opens a comment
        have hhead : c = '/' → ∀ d ys, stripComments rest = d :: ys → d ≠ '*' ∧ d ≠ '/' := by
          intro hslash d ys hout
          have hnot : ¬(rest.head? = some '*' ∨ rest.head? = some '/') := fun hx => hc ⟨hslash, hx⟩
          cases rest with
          | nil => rw [stripComments_nil] at hout; cases hout
          | cons e tail =>
            have he1 : e ≠ '*' := fun he => hnot (.inl (by simp [he]))
            have he2 : e ≠ '/' := fun he => hnot (.inr (by simp [he]))
            rw [stripComments_other e tail (by simp [he2])] at hout
            have := List.head_eq_of_cons_eq hout
            subst this
            exact ⟨he1, he2⟩
        constructor
        · intro xs ys he
          cases xs with
          | nil =>
            have ⟨h3, h4⟩ := List.cons.inj he
            exact (hhead h3 '*' ys h4).1 rfl
          | cons x xs => exact h1 xs ys (List.cons.inj he).2
        · intro xs ys he
          cases xs with
          | nil =>
            have ⟨h3, h4⟩ := List.cons.inj he
            exact (hhead h3 '/' ys h4).2 rfl
          | cons x xs => exact h2 xs ys (List.cons.inj he).2

/-- Comment stripping is idempotent. -/
theorem stripComments_idempotent (input : List Char) :
    stripComments (stripComments input) = stripComments input :=
  have ⟨h1, h2⟩ := stripComments_no_opener input
  stripComments_of_no_opener _ h1 h2

end Bap.Proofs.API
