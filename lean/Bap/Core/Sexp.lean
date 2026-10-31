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

def parseMany (input : String) : Except String (List Sexp) := do
  let chars := input.toList
  parseManyAux (chars.length * 2 + 2) chars []

def parse (input : String) : Except String Sexp := do
  let chars := input.toList
  let (value, rest) ← parseOne (chars.length * 2 + 2) chars
  match skipSpace rest with
  | [] => .ok value
  | _ => .error "trailing input after S-expression"

private def needsQuotes (value : String) : Bool :=
  value.isEmpty ∨ value.toList.head? = some '\'' ∨ value.toList.any fun c =>
    c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';' ∨ c = '"' ∨ c = '\\'

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
