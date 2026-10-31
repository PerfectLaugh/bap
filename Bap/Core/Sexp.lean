import Std

namespace Bap

inductive Sexp where
  | atom (value : String)
  | list (items : List Sexp)
  deriving BEq, Repr

mutual
  def Sexp.decEq : (x y : Sexp) → Decidable (x = y)
    | .atom a, .atom b =>
      if h : a = b then
        isTrue (congrArg Sexp.atom h)
      else
        isFalse fun eq => by cases eq; exact h rfl
    | .list xs, .list ys =>
      match listDecEq xs ys with
      | isTrue h => isTrue (congrArg Sexp.list h)
      | isFalse h => isFalse fun eq => by cases eq; exact h rfl
    | .atom _, .list _ => isFalse (by intro h; contradiction)
    | .list _, .atom _ => isFalse (by intro h; contradiction)

  def listDecEq : (xs ys : List Sexp) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
      match Sexp.decEq x y, listDecEq xs ys with
      | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
      | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
      | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
    | [], _ :: _ => isFalse (by intro h; contradiction)
    | _ :: _, [] => isFalse (by intro h; contradiction)
end

instance : DecidableEq Sexp := Sexp.decEq

namespace Sexp

def tagged (tag : String) (items : List Sexp := []) : Sexp :=
  .list (.atom tag :: items)

def asAtom : Sexp → Except String String
  | .atom value => .ok value
  | value => .error s!"expected an atom, got {repr value}"

def asList : Sexp → Except String (List Sexp)
  | .list items => .ok items
  | value => .error s!"expected a list, got {repr value}"

def expectTagged (tag : String) (arity : Nat) (value : Sexp) : Except String (List Sexp) := do
  let items ← asList value
  match items with
  | .atom actual :: args =>
    if actual = tag ∧ args.length = arity then
      .ok args
    else
      .error s!"expected ({tag} ...) with arity {arity}"
  | _ => .error s!"expected ({tag} ...) with arity {arity}"

def nat (value : Sexp) : Except String Nat := do
  let atom ← asAtom value
  match atom.toNat? with
  | some value => .ok value
  | none => .error s!"expected a natural number, got {atom}"

def dropComment : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => dropComment rest

theorem dropComment_length_le : (input : List Char) → (dropComment input).length ≤ input.length
  | [] => by simp [dropComment]
  | '\n' :: rest => by simp [dropComment]
  | c :: rest => by
    by_cases h : c = '\n'
    · subst h
      simp [dropComment]
    · have := dropComment_length_le rest
      simp only [dropComment, List.length_cons]
      omega

def skipSpace : List Char → List Char
  | [] => []
  | c :: rest =>
    if c.isWhitespace then
      skipSpace rest
    else if c = ';' then
      skipSpace (dropComment rest)
    else
      c :: rest
termination_by input => input.length
decreasing_by
  · simp
  · have := dropComment_length_le rest
    simp only [List.length_cons]
    omega

private def escape : Char → List Char
  | '"' => ['\\', '"']
  | '\\' => ['\\', '\\']
  | '\n' => ['\\', 'n']
  | '\r' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | c => [c]

private def parseEscaped : Char → Except String Char
  | 'n' => .ok '\n'
  | 'r' => .ok '\r'
  | 't' => .ok '\t'
  | '\\' => .ok '\\'
  | '"' => .ok '"'
  | c => .error s!"unsupported escape sequence \\{c}"

private def parseQuoted : Nat → List Char → Except String (String × List Char)
  | 0, _ => .error "unterminated quoted atom"
  | _ + 1, [] => .error "unterminated quoted atom"
  | _fuel + 1, '"' :: rest => .ok ("", rest)
  | fuel + 1, '\\' :: c :: rest => do
    let (tail, remaining) ← parseQuoted fuel rest
    .ok (String.ofList [← parseEscaped c] ++ tail, remaining)
  | fuel + 1, c :: rest => do
    let (tail, remaining) ← parseQuoted fuel rest
    .ok (String.ofList [c] ++ tail, remaining)

private def parseAtom (input : List Char) : String × List Char :=
  let atom := input.takeWhile fun c => !(c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';')
  (String.ofList atom, input.drop atom.length)

mutual
  def parseOne : Nat → List Char → Except String (Sexp × List Char)
    | 0, _ => .error "S-expression parser fuel exhausted"
    | fuel + 1, input =>
      match skipSpace input with
      | [] => .error "expected an S-expression"
      | '(' :: rest => do
        let (items, remaining) ← parseList fuel rest
        .ok (.list items, remaining)
      | ')' :: _ => .error "unexpected closing parenthesis"
      | '\'' :: rest => do
        let (value, remaining) ← parseOne fuel rest
        .ok (.list [.atom "quote", value], remaining)
      | '"' :: rest => do
        let (value, remaining) ← parseQuoted (rest.length + 1) rest
        .ok (.atom value, remaining)
      | input =>
        let (value, remaining) := parseAtom input
        .ok (.atom value, remaining)

  def parseList : Nat → List Char → Except String (List Sexp × List Char)
    | 0, _ => .error "unterminated S-expression list"
    | fuel + 1, input =>
      match skipSpace input with
      | [] => .error "unterminated S-expression list"
      | ')' :: rest => .ok ([], rest)
      | input => do
        let (item, rest) ← parseOne fuel input
        let (items, remaining) ← parseList fuel rest
        .ok (item :: items, remaining)
end

/-! `parseOne` and `parseList` without measuring what is left at each quoted atom, and without a stack frame or
a string copy per item. Quoted atoms run out of input before they run out of the fuel `parseOne` gives them, so
the fast ones need none: an error in the rest of the atom wins over a bad escape, and the last bad escape over the others. -/

private def parseQuotedFast : List Char → String → Option String → Except String (String × List Char)
  | [], _, _ => .error "unterminated quoted atom"
  | '"' :: rest, acc, bad =>
    match bad with
    | some error => .error error
    | none => .ok (acc, rest)
  | '\\' :: c :: rest, acc, bad =>
    match parseEscaped c with
    | .ok unescaped => parseQuotedFast rest (acc.push unescaped) bad
    | .error error => parseQuotedFast rest acc (some error)
  | c :: rest, acc, bad => parseQuotedFast rest (acc.push c) bad

private theorem push_append (acc tail : String) (c : Char) :
    acc ++ (String.ofList [c] ++ tail) = acc.push c ++ tail := by
  apply String.toList_injective
  simp

private theorem parseQuotedFast_eq (fuel : Nat) (input : List Char) (acc : String) (bad : Option String)
    (h : input.length < fuel) :
    parseQuotedFast input acc bad =
      match parseQuoted fuel input with
      | .error error => .error error
      | .ok (tail, remaining) =>
        match bad with
        | some error => .error error
        | none => .ok (acc ++ tail, remaining) := by
  induction fuel generalizing input acc bad with
  | zero => omega
  | succ fuel ih =>
    have after : ∀ (rest : List Char) (c : Char), rest.length < fuel →
        parseQuotedFast rest (acc.push c) bad =
          match (do
            let (tail, remaining) ← parseQuoted fuel rest
            .ok (String.ofList [c] ++ tail, remaining) : Except String (String × List Char)) with
          | .error error => .error error
          | .ok (tail, remaining) =>
            match bad with
            | some error => .error error
            | none => .ok (acc ++ tail, remaining) := by
      intro rest c hl
      rw [ih rest _ _ hl]
      simp only [bind, Except.bind]
      cases parseQuoted fuel rest with
      | error error => rfl
      | ok result =>
        obtain ⟨tail, remaining⟩ := result
        cases bad
        · simp only [push_append]
        · rfl
    cases input with
    | nil => simp [parseQuotedFast, parseQuoted]
    | cons c rest =>
      by_cases h1 : c = '"'
      · subst h1
        cases bad <;> simp [parseQuotedFast, parseQuoted]
      by_cases h2 : c = '\\'
      · subst h2
        cases rest with
        | nil =>
          obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
          simp [parseQuotedFast, parseQuoted, bind, Except.bind]
        | cons d rest =>
          have hl : rest.length < fuel := by simp only [List.length_cons] at h; omega
          rw [parseQuotedFast, parseQuoted]
          cases he : parseEscaped d with
          | ok unescaped =>
            dsimp only
            rw [after rest unescaped hl]
            simp only [bind, Except.bind]
          | error error =>
            dsimp only
            rw [ih rest _ _ hl]
            simp only [bind, Except.bind]
            cases parseQuoted fuel rest <;> rfl
      · rw [parseQuotedFast, parseQuoted]
        · exact after rest c (by simpa using h)
        all_goals simp_all

mutual
  private def parseOneFast : Nat → List Char → Except String (Sexp × List Char)
    | 0, _ => .error "S-expression parser fuel exhausted"
    | fuel + 1, input =>
      match skipSpace input with
      | [] => .error "expected an S-expression"
      | '(' :: rest =>
        match parseListFast fuel rest [] with
        | .error error => .error error
        | .ok (items, remaining) => .ok (.list items, remaining)
      | ')' :: _ => .error "unexpected closing parenthesis"
      | '\'' :: rest =>
        match parseOneFast fuel rest with
        | .error error => .error error
        | .ok (value, remaining) => .ok (.list [.atom "quote", value], remaining)
      | '"' :: rest =>
        match parseQuotedFast rest "" none with
        | .error error => .error error
        | .ok (value, remaining) => .ok (.atom value, remaining)
      | input =>
        let (value, remaining) := parseAtom input
        .ok (.atom value, remaining)

  private def parseListFast : Nat → List Char → List Sexp → Except String (List Sexp × List Char)
    | 0, _, _ => .error "unterminated S-expression list"
    | fuel + 1, input, acc =>
      match skipSpace input with
      | [] => .error "unterminated S-expression list"
      | ')' :: rest => .ok (acc.reverse, rest)
      | input =>
        match parseOneFast fuel input with
        | .error error => .error error
        | .ok (item, rest) => parseListFast fuel rest (item :: acc)
end

private theorem parseFast_eq (fuel : Nat) :
    (∀ input, parseOneFast fuel input = parseOne fuel input) ∧
      ∀ input acc, parseListFast fuel input acc =
        match parseList fuel input with
        | .error error => .error error
        | .ok (items, remaining) => .ok (acc.reverse ++ items, remaining) := by
  induction fuel with
  | zero =>
    refine ⟨fun input => ?_, fun input acc => ?_⟩ <;> simp [parseOneFast, parseOne, parseListFast, parseList]
  | succ fuel ih =>
    obtain ⟨hone, hlist⟩ := ih
    refine ⟨fun input => ?_, fun input acc => ?_⟩
    · rw [parseOneFast, parseOne]
      split
      · rfl
      · simp only [hlist, bind, Except.bind]
        cases parseList fuel _ <;> simp
      · rfl
      · simp only [hone, bind, Except.bind]
        cases parseOne fuel _ <;> rfl
      · rename_i rest _
        rw [parseQuotedFast_eq (rest.length + 1) rest "" none (Nat.lt_succ_self _)]
        simp only [bind, Except.bind]
        cases parseQuoted (rest.length + 1) rest <;> simp
      · rfl
    · rw [parseListFast, parseList]
      split
      · rfl
      · simp
      · simp only [hone, bind, Except.bind]
        cases parseOne fuel _ with
        | error error => rfl
        | ok result =>
          simp only [hlist]
          cases parseList fuel _ <;> simp

@[csimp] private theorem parseOne_eq_fast : @parseOne = @parseOneFast :=
  funext fun fuel => funext fun input => ((parseFast_eq fuel).1 input).symm

private def parseListStart (fuel : Nat) (input : List Char) : Except String (List Sexp × List Char) :=
  parseListFast fuel input []

@[csimp] private theorem parseList_eq_fast : @parseList = @parseListStart := by
  funext fuel input
  simp only [parseListStart, (parseFast_eq fuel).2]
  cases parseList fuel input <;> simp

private def parseManyAux : Nat → List Char → List Sexp → Except String (List Sexp)
  | 0, _, _ => .error "S-expression parser fuel exhausted"
  | fuel + 1, input, results =>
    match skipSpace input with
    | [] => .ok results.reverse
    | _ => do
      let (value, rest) ← parseOne fuel input
      parseManyAux fuel rest (value :: results)

/-! Parsing an ASCII string by its bytes, with the place in them for the list of what is left. -/

private def byteChar (byte : UInt8) : Char := Char.ofNat byte.toNat

private def charAt (bytes : ByteArray) (index : Nat) : Char := byteChar (bytes.get! index)

/-- The characters from `index` on. -/
private def view (bytes : ByteArray) (index : Nat) : List Char := (bytes.data.toList.drop index).map byteChar

private theorem view_cons (bytes : ByteArray) (index : Nat) (h : index < bytes.size) :
    view bytes index = charAt bytes index :: view bytes (index + 1) := by
  have hlen : index < bytes.data.toList.length := by simpa using h
  have hget : bytes.get! index = bytes.data.toList[index] := by
    have hdata : index < bytes.data.size := by simpa using h
    show bytes.data[index]! = _
    rw [getElem!_pos bytes.data index hdata]
    simp
  simp only [view, charAt, hget]
  rw [List.drop_eq_getElem_cons hlen]
  rfl

private theorem view_nil (bytes : ByteArray) (index : Nat) (h : bytes.size ≤ index) : view bytes index = [] := by
  have hlen : bytes.data.toList.length ≤ index := by simpa using h
  simp [view, List.drop_eq_nil_of_le hlen]

private def dropCommentBytes (bytes : ByteArray) : Nat → Nat → Nat
  | 0, index => index
  | fuel + 1, index =>
    if index < bytes.size then
      if charAt bytes index = '\n' then index + 1 else dropCommentBytes bytes fuel (index + 1)
    else index

private theorem dropCommentBytes_spec (bytes : ByteArray) (fuel index : Nat) (h : bytes.size - index ≤ fuel) :
    view bytes (dropCommentBytes bytes fuel index) = dropComment (view bytes index) ∧ index ≤ dropCommentBytes bytes fuel index := by
  induction fuel generalizing index with
  | zero =>
    have hle : bytes.size ≤ index := by omega
    simp [dropCommentBytes, view_nil bytes index hle, dropComment]
  | succ fuel ih =>
    rw [dropCommentBytes]
    split
    · rename_i hlt
      rw [view_cons bytes index hlt]
      split
      · rename_i hc
        rw [hc]
        simp [dropComment]
      · rename_i hc
        obtain ⟨h1, h2⟩ := ih (index + 1) (by omega)
        refine ⟨?_, by omega⟩
        rw [h1]
        rw [dropComment]
        simp [hc]
    · rename_i hge
      simp [view_nil bytes index (by omega), dropComment]

private def skipSpaceBytes (bytes : ByteArray) : Nat → Nat → Nat
  | 0, index => index
  | fuel + 1, index =>
    if index < bytes.size then
      let c := charAt bytes index
      if c.isWhitespace then skipSpaceBytes bytes fuel (index + 1)
      else if c = ';' then skipSpaceBytes bytes fuel (dropCommentBytes bytes (bytes.size - (index + 1)) (index + 1))
      else index
    else index

private theorem skipSpaceBytes_spec (bytes : ByteArray) (fuel index : Nat) (h : bytes.size - index ≤ fuel) :
    view bytes (skipSpaceBytes bytes fuel index) = skipSpace (view bytes index) := by
  induction fuel generalizing index with
  | zero =>
    have hle : bytes.size ≤ index := by omega
    simp [skipSpaceBytes, view_nil bytes index hle, skipSpace]
  | succ fuel ih =>
    rw [skipSpaceBytes]
    split
    · rename_i hlt
      rw [view_cons bytes index hlt, skipSpace]
      dsimp only
      split
      · exact ih _ (by omega)
      · split
        · obtain ⟨h1, h2⟩ := dropCommentBytes_spec bytes (bytes.size - (index + 1)) (index + 1) (by omega)
          rw [← h1]
          exact ih _ (by omega)
        · exact view_cons bytes index hlt
    · rename_i hge
      simp [view_nil bytes index (by omega), skipSpace]

/-- Whether a character is in an atom. -/
private def inAtom (c : Char) : Bool := !(c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';')

private def atomBytes (bytes : ByteArray) : Nat → Nat → String → String × Nat
  | 0, index, acc => (acc, index)
  | fuel + 1, index, acc =>
    if index < bytes.size then
      let c := charAt bytes index
      if inAtom c then atomBytes bytes fuel (index + 1) (acc.push c) else (acc, index)
    else (acc, index)

private theorem atomBytes_spec (bytes : ByteArray) (fuel index : Nat) (acc : String) (h : bytes.size - index ≤ fuel) :
    (atomBytes bytes fuel index acc).1 = acc ++ String.ofList ((view bytes index).takeWhile inAtom) ∧
      view bytes (atomBytes bytes fuel index acc).2 = (view bytes index).dropWhile inAtom := by
  induction fuel generalizing index acc with
  | zero =>
    have hle : bytes.size ≤ index := by omega
    simp [atomBytes, view_nil bytes index hle]
  | succ fuel ih =>
    rw [atomBytes]
    split
    · rename_i hlt
      have hv := view_cons bytes index hlt
      dsimp only
      by_cases hc : inAtom (charAt bytes index) = true
      · rw [ite_eq_left hc, hv]
        obtain ⟨h1, h2⟩ := ih (index + 1) (acc.push (charAt bytes index)) (by omega)
        simp only [List.takeWhile_cons, List.dropWhile_cons, hc, ↓reduceIte]
        refine ⟨?_, h2⟩
        rw [h1]
        apply String.toList_injective
        simp
      · rw [ite_eq_right hc, hv]
        have hf : inAtom (charAt bytes index) = false := by simpa using hc
        simp [hf]
    · rename_i hge
      simp [view_nil bytes index (by omega)]

private theorem parseAtom_eq (input : List Char) :
    parseAtom input = (String.ofList (input.takeWhile inAtom), input.dropWhile inAtom) := by
  have hsplit := List.takeWhile_append_dropWhile (p := inAtom) (l := input)
  have hdrop : input.drop (input.takeWhile inAtom).length = input.dropWhile inAtom := by
    have := List.drop_left (l₁ := input.takeWhile inAtom) (l₂ := input.dropWhile inAtom)
    rwa [hsplit] at this
  simp only [parseAtom]
  exact Prod.ext rfl hdrop

private def quotedBytes (bytes : ByteArray) : Nat → Nat → String → Option String → Except String (String × Nat)
  | 0, _, _, _ => .error "unterminated quoted atom"
  | fuel + 1, index, acc, bad =>
    if index < bytes.size then
      let c := charAt bytes index
      if c = '"' then
        match bad with
        | some error => .error error
        | none => .ok (acc, index + 1)
      else if c = '\\' && index + 1 < bytes.size then
        match parseEscaped (charAt bytes (index + 1)) with
        | .ok unescaped => quotedBytes bytes fuel (index + 2) (acc.push unescaped) bad
        | .error error => quotedBytes bytes fuel (index + 2) acc (some error)
      else quotedBytes bytes fuel (index + 1) (acc.push c) bad
    else .error "unterminated quoted atom"

/-- What is left as a list, in a result with the place in the bytes. -/
private def viewResult {α : Type} (bytes : ByteArray) : Except String (α × Nat) → Except String (α × List Char)
  | .error error => .error error
  | .ok (value, index) => .ok (value, view bytes index)

private theorem quoted_close (rest : List Char) (acc : String) (bad : Option String) :
    parseQuotedFast ('"' :: rest) acc bad =
      match bad with
      | some error => .error error
      | none => .ok (acc, rest) := by
  cases bad <;> simp [parseQuotedFast]

private theorem quoted_escape (c : Char) (rest : List Char) (acc : String) (bad : Option String) :
    parseQuotedFast ('\\' :: c :: rest) acc bad =
      match parseEscaped c with
      | .ok unescaped => parseQuotedFast rest (acc.push unescaped) bad
      | .error error => parseQuotedFast rest acc (some error) := by
  simp [parseQuotedFast]

private theorem quoted_other (c : Char) (rest : List Char) (acc : String) (bad : Option String) (h1 : c ≠ '"')
    (h2 : c ≠ '\\' ∨ rest = []) :
    parseQuotedFast (c :: rest) acc bad = parseQuotedFast rest (acc.push c) bad := by
  rw [parseQuotedFast]
  · exact h1
  · intro d tail hc he
    rcases h2 with h2 | h2
    · exact h2 hc
    · rw [h2] at he
      cases he

private theorem quotedBytes_spec (bytes : ByteArray) (fuel index : Nat) (acc : String) (bad : Option String)
    (h : bytes.size - index < fuel) :
    viewResult bytes (quotedBytes bytes fuel index acc bad) = parseQuotedFast (view bytes index) acc bad := by
  induction fuel generalizing index acc bad with
  | zero => omega
  | succ fuel ih =>
    rw [quotedBytes.eq_def]
    dsimp only
    split
    · rename_i hlt
      rw [view_cons bytes index hlt]
      split
      · rename_i hc
        rw [hc, quoted_close]
        cases bad <;> rfl
      · rename_i hc
        split
        · rename_i hesc
          have ⟨hb, hn⟩ : charAt bytes index = '\\' ∧ index + 1 < bytes.size := by simpa using hesc
          rw [hb, view_cons bytes (index + 1) hn, quoted_escape]
          cases parseEscaped (charAt bytes (index + 1)) with
          | ok unescaped => exact ih _ _ _ (by omega)
          | error error => exact ih _ _ _ (by omega)
        · rename_i hesc
          have hrest : charAt bytes index ≠ '\\' ∨ view bytes (index + 1) = [] := by
            by_cases hb : charAt bytes index = '\\'
            · refine .inr (view_nil bytes (index + 1) ?_)
              have := hesc
              simp only [hb, decide_true, Bool.true_and, decide_eq_true_eq] at this
              omega
            · exact .inl hb
          rw [ih _ _ _ (by omega), quoted_other _ _ _ _ hc hrest]
    · rename_i hge
      simp [view_nil bytes index (by omega), parseQuotedFast, viewResult]

mutual
  private def parseOneBytes (bytes : ByteArray) : Nat → Nat → Except String (Sexp × Nat)
    | 0, _ => .error "S-expression parser fuel exhausted"
    | fuel + 1, index =>
      let index := skipSpaceBytes bytes bytes.size index
      if index < bytes.size then
        let c := charAt bytes index
        if c = '(' then
          match parseListBytes bytes fuel (index + 1) [] with
          | .error error => .error error
          | .ok (items, remaining) => .ok (.list items, remaining)
        else if c = ')' then .error "unexpected closing parenthesis"
        else if c = '\'' then
          match parseOneBytes bytes fuel (index + 1) with
          | .error error => .error error
          | .ok (value, remaining) => .ok (.list [.atom "quote", value], remaining)
        else if c = '"' then
          match quotedBytes bytes (bytes.size + 1) (index + 1) "" none with
          | .error error => .error error
          | .ok (value, remaining) => .ok (.atom value, remaining)
        else
          let (value, remaining) := atomBytes bytes bytes.size index ""
          .ok (.atom value, remaining)
      else .error "expected an S-expression"

  private def parseListBytes (bytes : ByteArray) : Nat → Nat → List Sexp → Except String (List Sexp × Nat)
    | 0, _, _ => .error "unterminated S-expression list"
    | fuel + 1, index, acc =>
      let index := skipSpaceBytes bytes bytes.size index
      if index < bytes.size then
        if charAt bytes index = ')' then .ok (acc.reverse, index + 1)
        else
          match parseOneBytes bytes fuel index with
          | .error error => .error error
          | .ok (item, rest) => parseListBytes bytes fuel rest (item :: acc)
      else .error "unterminated S-expression list"
end

private theorem parseBytes_spec (bytes : ByteArray) (fuel : Nat) :
    (∀ index, viewResult bytes (parseOneBytes bytes fuel index) = parseOneFast fuel (view bytes index)) ∧
      ∀ index acc, viewResult bytes (parseListBytes bytes fuel index acc) = parseListFast fuel (view bytes index) acc := by
  induction fuel with
  | zero =>
    refine ⟨fun index => ?_, fun index acc => ?_⟩ <;> simp [parseOneBytes, parseOneFast, parseListBytes, parseListFast, viewResult]
  | succ fuel ih =>
    obtain ⟨hone, hlist⟩ := ih
    have hskip : ∀ index, view bytes (skipSpaceBytes bytes bytes.size index) = skipSpace (view bytes index) :=
      fun index => skipSpaceBytes_spec bytes _ index (by omega)
    refine ⟨fun index => ?_, fun index acc => ?_⟩
    · rw [parseOneBytes, parseOneFast, ← hskip]
      dsimp only
      generalize skipSpaceBytes bytes bytes.size index = j
      split
      · rename_i hlt
        have hv := view_cons bytes j hlt
        rw [hv]
        generalize charAt bytes j = c at hv
        split
        · rename_i h1
          subst h1
          show _ = (match parseListFast fuel (view bytes (j + 1)) [] with
            | .error error => .error error
            | .ok (items, remaining) => .ok (.list items, remaining) : Except String (Sexp × List Char))
          rw [← hlist (j + 1) []]
          cases parseListBytes bytes fuel (j + 1) [] with
          | error => rfl
          | ok result => rfl
        · rename_i h1
          split
          · rename_i h2
            subst h2
            rfl
          · rename_i h2
            split
            · rename_i h3
              subst h3
              show _ = (match parseOneFast fuel (view bytes (j + 1)) with
                | .error error => .error error
                | .ok (value, remaining) => .ok (.list [.atom "quote", value], remaining) : Except String (Sexp × List Char))
              rw [← hone (j + 1)]
              cases parseOneBytes bytes fuel (j + 1) with
              | error => rfl
              | ok result => rfl
            · rename_i h3
              split
              · rename_i h4
                subst h4
                show _ = (match parseQuotedFast (view bytes (j + 1)) "" none with
                  | .error error => .error error
                  | .ok (value, remaining) => .ok (.atom value, remaining) : Except String (Sexp × List Char))
                rw [← quotedBytes_spec bytes (bytes.size + 1) (j + 1) "" none (by omega)]
                cases quotedBytes bytes (bytes.size + 1) (j + 1) "" none with
                | error => rfl
                | ok result => rfl
              · rename_i h4
                obtain ⟨ha1, ha2⟩ := atomBytes_spec bytes bytes.size j "" (by omega)
                have hmatch : (match c :: view bytes (j + 1) with
                    | [] => (Except.error "expected an S-expression" : Except String (Sexp × List Char))
                    | '(' :: rest =>
                      match parseListFast fuel rest [] with
                      | .error error => .error error
                      | .ok (items, remaining) => .ok (.list items, remaining)
                    | ')' :: _ => .error "unexpected closing parenthesis"
                    | '\'' :: rest =>
                      match parseOneFast fuel rest with
                      | .error error => .error error
                      | .ok (value, remaining) => .ok (.list [.atom "quote", value], remaining)
                    | '"' :: rest =>
                      match parseQuotedFast rest "" none with
                      | .error error => .error error
                      | .ok (value, remaining) => .ok (.atom value, remaining)
                    | input =>
                      let (value, remaining) := parseAtom input
                      .ok (.atom value, remaining)) =
                    .ok (.atom (parseAtom (c :: view bytes (j + 1))).1, (parseAtom (c :: view bytes (j + 1))).2) := by
                  split
                  · rename_i heq; cases heq
                  · rename_i heq; cases heq; exact absurd rfl h1
                  · rename_i heq; cases heq; exact absurd rfl h2
                  · rename_i heq; cases heq; exact absurd rfl h3
                  · rename_i heq; cases heq; exact absurd rfl h4
                  · rfl
                rw [hmatch, parseAtom_eq]
                rw [hv] at ha1 ha2
                simp only [viewResult]
                rw [ha2, ha1]
                simp
      · rename_i hge
        simp [view_nil bytes j (by omega), viewResult]
    · rw [parseListBytes, parseListFast, ← hskip]
      generalize skipSpaceBytes bytes bytes.size index = j
      split
      · rename_i hlt
        have hv := view_cons bytes j hlt
        split
        · rename_i h1
          rw [hv, h1]
          rfl
        · rename_i h1
          have hmatch : (match view bytes j with
              | [] => (Except.error "unterminated S-expression list" : Except String (List Sexp × List Char))
              | ')' :: rest => .ok (acc.reverse, rest)
              | input =>
                match parseOneFast fuel input with
                | .error error => .error error
                | .ok (item, rest) => parseListFast fuel rest (item :: acc)) =
              (match parseOneFast fuel (view bytes j) with
                | .error error => .error error
                | .ok (item, rest) => parseListFast fuel rest (item :: acc)) := by
            rw [hv]
            generalize charAt bytes j = d at h1
            split
            · rename_i heq; cases heq
            · rename_i heq; cases heq; exact absurd rfl h1
            · rfl
          rw [hmatch, ← hone j]
          cases parseOneBytes bytes fuel j with
          | error => rfl
          | ok result => exact hlist _ _
      · rename_i hge
        simp [view_nil bytes j (by omega), viewResult]

private theorem encode_size_ge (chars : List Char) : chars.length ≤ chars.utf8Encode.size := by
  induction chars with
  | nil => simp
  | cons c rest ih =>
    rw [List.utf8Encode_cons, ByteArray.size_append, List.utf8Encode_singleton]
    have := c.utf8Size_pos
    simp only [List.size_toByteArray, String.length_utf8EncodeChar, List.length_cons]
    omega

private theorem byteChar_ascii (c : Char) (h : c.utf8Size = 1) : byteChar c.val.toUInt8 = c := by
  have hval : c.val.toNat ≤ 127 := by
    have := Char.utf8Size_eq_one_iff.1 h
    simpa [UInt32.le_iff_toNat_le] using this
  have hbyte : c.val.toUInt8.toNat = c.toNat := by
    simp only [UInt32.toNat_toUInt8, Char.toNat]
    omega
  unfold byteChar
  rw [hbyte]
  exact Char.ofNat_toNat c

/-- The characters of a string of as many bytes as characters are its bytes. -/
private theorem ascii_chars (chars : List Char) (h : chars.utf8Encode.size = chars.length) :
    chars.utf8Encode.data.toList.map byteChar = chars := by
  induction chars with
  | nil => simp
  | cons c rest ih =>
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, ByteArray.size_append, List.size_toByteArray] at h
    have hrest := encode_size_ge rest
    have hpos := c.utf8Size_pos
    simp only [String.length_utf8EncodeChar, List.length_cons] at h
    have h1 : c.utf8Size = 1 := by omega
    have h2 : rest.utf8Encode.size = rest.length := by omega
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton h1]
    simp only [ByteArray.data_append, List.data_toByteArray, Array.toList_append, List.map_append, ih h2]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [byteChar_ascii c h1]

private theorem view_string (input : String) (h : input.length = input.utf8ByteSize) :
    view input.toUTF8 0 = input.toList := by
  have hsize : input.toList.utf8Encode.size = input.toList.length := by
    rw [String.utf8Encode_toList, String.length_toList, String.size_toByteArray, h]
  have := ascii_chars input.toList hsize
  rw [String.utf8Encode_toList] at this
  simpa [view] using this

def parseMany (input : String) : Except String (List Sexp) := do
  let chars := input.toList
  parseManyAux (chars.length * 2 + 2) chars []

def parse (input : String) : Except String Sexp := do
  let chars := input.toList
  let (value, rest) ← parseOne (chars.length * 2 + 2) chars
  match skipSpace rest with
  | [] => .ok value
  | _ => .error "trailing input after S-expression"

private def parseManyBytes (bytes : ByteArray) : Nat → Nat → List Sexp → Except String (List Sexp)
  | 0, _, _ => .error "S-expression parser fuel exhausted"
  | fuel + 1, index, results =>
    if skipSpaceBytes bytes bytes.size index < bytes.size then
      match parseOneBytes bytes fuel index with
      | .error error => .error error
      | .ok (value, rest) => parseManyBytes bytes fuel rest (value :: results)
    else .ok results.reverse

private theorem parseOne_view (bytes : ByteArray) (fuel index : Nat) :
    viewResult bytes (parseOneBytes bytes fuel index) = parseOne fuel (view bytes index) := by
  rw [parseOne_eq_fast]
  exact (parseBytes_spec bytes fuel).1 index

private theorem skip_view (bytes : ByteArray) (index : Nat) :
    skipSpace (view bytes index) = view bytes (skipSpaceBytes bytes bytes.size index) :=
  (skipSpaceBytes_spec bytes _ index (by omega)).symm

private theorem parseManyBytes_eq (bytes : ByteArray) (fuel index : Nat) (results : List Sexp) :
    parseManyBytes bytes fuel index results = parseManyAux fuel (view bytes index) results := by
  induction fuel generalizing index results with
  | zero => rfl
  | succ fuel ih =>
    rw [parseManyBytes, parseManyAux, skip_view]
    split
    · rename_i hlt
      rw [view_cons bytes _ hlt]
      have hv := parseOne_view bytes fuel index
      cases hr : parseOneBytes bytes fuel index with
      | error error =>
        rw [hr] at hv
        simp only [viewResult] at hv
        simp only [bind, Except.bind, ← hv]
      | ok result =>
        rw [hr] at hv
        obtain ⟨value, rest⟩ := result
        simp only [viewResult] at hv
        simp only [bind, Except.bind, ← hv]
        exact ih _ _
    · rename_i hge
      rw [view_nil bytes _ (by omega)]

/-- `parseMany`, by the bytes of an ASCII string. -/
private def parseManyFast (input : String) : Except String (List Sexp) :=
  if input.length = input.utf8ByteSize then
    let bytes := input.toUTF8
    parseManyBytes bytes (bytes.size * 2 + 2) 0 []
  else
    let chars := input.toList
    parseManyAux (chars.length * 2 + 2) chars []

@[csimp] private theorem parseMany_eq_fast : @parseMany = @parseManyFast := by
  funext input
  simp only [parseMany, parseManyFast]
  split
  · rename_i h
    rw [parseManyBytes_eq, view_string input h]
    have : input.toUTF8.size = input.toList.length := by
      rw [String.length_toList, h]
      rfl
    rw [this]
  · rfl

/-- `parse`, by the bytes of an ASCII string. -/
private def parseFast (input : String) : Except String Sexp :=
  if input.length = input.utf8ByteSize then
    let bytes := input.toUTF8
    match parseOneBytes bytes (bytes.size * 2 + 2) 0 with
    | .error error => .error error
    | .ok (value, rest) =>
      if skipSpaceBytes bytes bytes.size rest < bytes.size then .error "trailing input after S-expression"
      else .ok value
  else do
    let chars := input.toList
    let (value, rest) ← parseOne (chars.length * 2 + 2) chars
    match skipSpace rest with
    | [] => .ok value
    | _ => .error "trailing input after S-expression"

@[csimp] private theorem parse_eq_fast : @parse = @parseFast := by
  funext input
  simp only [parse, parseFast]
  split
  · rename_i h
    have hsize : input.toUTF8.size = input.toList.length := by
      rw [String.length_toList, h]
      rfl
    have hv := parseOne_view input.toUTF8 (input.toUTF8.size * 2 + 2) 0
    rw [view_string input h] at hv
    rw [← hsize, ← hv]
    cases parseOneBytes input.toUTF8 (input.toUTF8.size * 2 + 2) 0 with
    | error => rfl
    | ok result =>
      obtain ⟨value, rest⟩ := result
      simp only [viewResult, bind, Except.bind, skip_view]
      by_cases hlt : skipSpaceBytes input.toUTF8 input.toUTF8.size rest < input.toUTF8.size
      · rw [ite_eq_left hlt, view_cons _ _ hlt]
      · rw [ite_eq_right hlt, view_nil _ _ (by omega)]
  · rfl

private def needsQuotes (value : String) : Bool :=
  value.isEmpty ∨ value.toList.head? = some '\'' ∨ value.toList.any fun c =>
    c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';' ∨ c = '"' ∨ c = '\\'

/-- A character that an atom can't have as it is. -/
private def specialChar (c : Char) : Bool :=
  c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';' ∨ c = '"' ∨ c = '\\'

/-- `needsQuotes`, which doesn't make a list of the characters of each atom. -/
private def needsQuotesFast (value : String) : Bool :=
  value.isEmpty || value.startsWith (fun c : Char => c == '\'') || value.contains specialChar

@[csimp] private theorem needsQuotes_eq_fast : @needsQuotes = @needsQuotesFast := by
  funext value
  have hany : (value.toList.any fun c => decide (c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';' ∨ c = '"' ∨ c = '\\')) =
      value.contains specialChar := by
    rw [String.contains_bool_eq]
    rfl
  have hstart : decide (value.toList.head? = some '\'') = value.startsWith (fun c : Char => c == '\'') := by
    rw [String.startsWith_bool_eq_head?]
    cases value.toList.head? with
    | none => simp
    | some head => by_cases h : head = '\'' <;> simp [h]
  rw [Bool.eq_iff_iff]
  simp only [needsQuotes, needsQuotesFast, ← hany, ← hstart, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, or_assoc]

def render : Sexp → String
  | .atom value =>
    if needsQuotes value then
      "\"" ++ String.ofList (value.toList.flatMap escape) ++ "\""
    else
      value
  | .list items => "(" ++ String.intercalate " " (items.map render) ++ ")"

/-! `render` into one string: a list otherwise copies what is under it, once per level. -/

private def renderAtomTo (acc value : String) : String :=
  if needsQuotes value then
    (acc.push '"' ++ String.ofList (value.toList.flatMap escape)).push '"'
  else
    acc ++ value

mutual
  private def renderTo (acc : String) : Sexp → String
    | .atom value => renderAtomTo acc value
    | .list [] => acc ++ "()"
    | .list (item :: rest) => (renderItemsTo (renderTo (acc.push '(') item) rest).push ')'

  /-- The items after the first one, each with its separator. -/
  private def renderItemsTo (acc : String) : List Sexp → String
    | [] => acc
    | item :: rest => renderItemsTo (renderTo (acc.push ' ') item) rest
end

mutual
  private theorem renderTo_eq (acc : String) : (value : Sexp) → renderTo acc value = acc ++ render value
    | .atom value => by
      rw [renderTo, renderAtomTo, render]
      split
      · apply String.toList_injective
        simp
      · rfl
    | .list [] => by
      rw [renderTo, render]
      simp [String.intercalate_nil]
    | .list (item :: rest) => by
      rw [renderTo, renderTo_eq (acc.push '(') item, renderItemsTo_eq (acc.push '(') (render item) rest, render, List.map_cons]
      apply String.toList_injective
      simp

  private theorem renderItemsTo_eq (acc first : String) : (items : List Sexp) →
      renderItemsTo (acc ++ first) items = acc ++ String.intercalate " " (first :: items.map render)
    | [] => by simp [renderItemsTo, String.intercalate_singleton]
    | item :: rest => by
      have happ : (acc ++ first).push ' ' ++ render item = acc ++ (first ++ " " ++ render item) := by
        apply String.toList_injective
        simp
      rw [renderItemsTo, renderTo_eq _ item, happ, renderItemsTo_eq acc _ rest, List.map_cons,
        String.intercalate_cons_cons, String.intercalate_cons_append]
end

private def renderFast (value : Sexp) : String := renderTo "" value

@[csimp] private theorem render_eq_fast : @render = @renderFast := by
  funext value
  simp [renderFast, renderTo_eq]

instance : ToString Sexp where
  toString := render

end Sexp
end Bap
