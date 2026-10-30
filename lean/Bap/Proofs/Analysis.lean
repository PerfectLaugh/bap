import Lean.Elab.Command
import Bap.Analysis.Xrefs
import Bap.Analysis.Callgraph
import Bap.Analysis.Strings
import Bap.Analysis.Slice
import Bap.Analysis.DynamicSlice
import Bap.Analysis.Taint
import Bap.Analysis.Propagate
import Bap.Analysis.DeadCode
import Bap.Analysis.Validate
import Bap.Analysis.Deflatten
import Bap.Analysis.Signatures
import Bap.Analysis.Protobuf

namespace Bap.Proofs.Analysis

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

section Xrefs
open Bap.Analysis.Xrefs
open_private Bap.Analysis.Xrefs in Bap.Analysis.Xrefs : constant memoryRefs stmtRefs insnRefs nearestStart spans

theorem xrefs_memoryRefs_shape (source : Nat) (exp : Bap.Bil.Exp) :
    ∀ xref ∈ memoryRefs source exp, xref.source = source ∧ xref.kind ≠ .call ∧ xref.kind ≠ .jump := by
  induction exp with
  | load memory address _ _ ihm iha =>
    intro xref h
    simp only [memoryRefs, List.mem_append, List.mem_map] at h
    rcases h with (⟨_, _, rfl⟩ | h) | h
    · simp
    · exact ihm xref h
    · exact iha xref h
  | store memory address value _ _ ihm iha ihv =>
    intro xref h
    simp only [memoryRefs, List.mem_append, List.mem_map] at h
    rcases h with ((⟨_, _, rfl⟩ | h) | h) | h
    · simp
    · exact ihm xref h
    · exact iha xref h
    · exact ihv xref h
  | bin _ _ _ ihl ihr | letIn _ _ _ ihl ihr | concat _ _ ihl ihr =>
    intro xref h
    simp only [memoryRefs, List.mem_append] at h
    exact h.elim (ihl xref) (ihr xref)
  | un _ _ ih | cast _ _ _ ih | extract _ _ _ ih =>
    intro xref h
    simp only [memoryRefs] at h
    exact ih xref h
  | ite _ _ _ ihc ihy ihn =>
    intro xref h
    simp only [memoryRefs, List.mem_append] at h
    rcases h with (h | h) | h
    · exact ihc xref h
    · exact ihy xref h
    · exact ihn xref h
  | int _ | var _ | unknown _ _ => simp [memoryRefs]

theorem xrefs_stmtRefs_shape (insn : Bap.Disasm.Insn) (stmt : Bap.Bil.Stmt) :
    ∀ xref ∈ stmtRefs insn stmt, xref.source = insn.address ∧ (xref.kind = .call → insn.flow = .call) := by
  induction stmt using stmtInduction with
  | move var value =>
    intro xref h
    simp only [stmtRefs] at h
    have := xrefs_memoryRefs_shape _ _ _ h
    simp_all
  | jmp target =>
    intro xref h
    simp only [stmtRefs, List.mem_append, List.mem_map] at h
    rcases h with ⟨address, _, rfl⟩ | h
    · by_cases hflow : insn.flow = .call <;> simp [hflow]
    · have := xrefs_memoryRefs_shape _ _ _ h
      simp_all
  | special message => simp [stmtRefs]
  | cpuExn number => simp [stmtRefs]
  | while_ condition body ih =>
    intro xref h
    simp only [stmtRefs, List.mem_append, List.mem_flatMap] at h
    rcases h with h | ⟨stmt, hs, h⟩
    · have := xrefs_memoryRefs_shape _ _ _ h
      simp_all
    · exact ih stmt hs xref h
  | ifElse condition yes no ihy ihn =>
    intro xref h
    simp only [stmtRefs, List.mem_append, List.mem_flatMap] at h
    rcases h with (h | ⟨stmt, hs, h⟩) | ⟨stmt, hs, h⟩
    · have := xrefs_memoryRefs_shape _ _ _ h
      simp_all
    · exact ihy stmt hs xref h
    · exact ihn stmt hs xref h

/-- Every recorded cross-reference originates at a disassembled instruction, and only an
instruction with call flow can produce a call reference. -/
theorem xrefs_create_source {project : Bap.Project.Project} {xref : Xref}
    (h : xref ∈ (create project).xrefs) :
    ∃ disasm insn, project.disasm = some disasm ∧ insn ∈ disasm.instructions ∧
      xref.source = insn.address ∧ (xref.kind = .call → insn.flow = .call) := by
  simp only [create] at h
  cases hd : project.disasm with
  | none => simp [hd] at h
  | some disasm =>
    simp only [hd, Option.map_some, Option.getD_some, List.mem_flatMap, insnRefs] at h
    obtain ⟨insn, hi, stmt, _, hx⟩ := h
    exact ⟨disasm, insn, rfl, hi, xrefs_stmtRefs_shape insn stmt xref hx⟩

/-- The index's function list is exactly the image's function symbols. -/
theorem xrefs_create_functions_iff (project : Bap.Project.Project) (symbol : Bap.Image.Symbol) :
    symbol ∈ (create project).functions ↔
      ∃ image, project.image = some image ∧ symbol ∈ image.symbols ∧ symbol.isFunction = true := by
  simp only [create]
  cases project.image <;> simp

theorem xrefs_mem_references_iff (index : Index) (kind : Kind) (target : Nat) (xref : Xref) :
    xref ∈ references index kind target ↔
      xref ∈ index.xrefs ∧ xref.kind = kind ∧ xref.target = target := by
  simp [references]

theorem xrefs_mem_callers_iff (index : Index) (target : Nat) (xref : Xref) :
    xref ∈ callers index target ↔
      xref ∈ index.xrefs ∧ xref.kind = .call ∧ xref.target = target :=
  xrefs_mem_references_iff index .call target xref

private def xrefs_pick (ok : Bap.Image.Symbol → Bool) (best : Option Bap.Image.Symbol)
    (symbol : Bap.Image.Symbol) : Option Bap.Image.Symbol :=
  if ok symbol && best.all (·.addr ≤ symbol.addr) then some symbol else best

private theorem xrefs_pick_fold (ok : Bap.Image.Symbol → Bool) (symbols : List Bap.Image.Symbol) :
    ∀ init : Option Bap.Image.Symbol,
      let result := symbols.foldl (xrefs_pick ok) init
      (∀ c, result = some c → (c ∈ symbols ∧ ok c = true) ∨ init = some c) ∧
      (∀ s ∈ symbols, ok s = true → ∃ c, result = some c ∧ s.addr ≤ c.addr) ∧
      (∀ c, init = some c → ∃ c', result = some c' ∧ c.addr ≤ c'.addr) := by
  induction symbols with
  | nil =>
    intro init
    exact ⟨fun c hc => .inr hc, by simp, fun c hc => ⟨c, hc, Nat.le_refl _⟩⟩
  | cons symbol rest ih =>
    intro init
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (xrefs_pick ok init symbol)
    have hsplit : (xrefs_pick ok init symbol = some symbol ∧ ok symbol = true) ∨
        xrefs_pick ok init symbol = init := by
      unfold xrefs_pick
      by_cases h : (ok symbol && init.all (·.addr ≤ symbol.addr)) = true
      · simp only [Bool.and_eq_true] at h
        simp [h]
      · simp [h]
    have hself : ok symbol = true →
        ∃ c, xrefs_pick ok init symbol = some c ∧ symbol.addr ≤ c.addr := by
      intro hok
      cases init with
      | none => exact ⟨symbol, by simp [xrefs_pick, hok], Nat.le_refl _⟩
      | some current =>
        by_cases hc : current.addr ≤ symbol.addr
        · exact ⟨symbol, by simp [xrefs_pick, hok, hc], Nat.le_refl _⟩
        · exact ⟨current, by simp [xrefs_pick, hc], by omega⟩
    have hinitNext : ∀ c, init = some c →
        ∃ c', xrefs_pick ok init symbol = some c' ∧ c.addr ≤ c'.addr := by
      intro c hc
      subst hc
      by_cases hgo : ok symbol = true ∧ c.addr ≤ symbol.addr
      · exact ⟨symbol, by simp [xrefs_pick, hgo], hgo.2⟩
      · refine ⟨c, ?_, Nat.le_refl _⟩
        simp only [xrefs_pick, Option.all_some, Bool.and_eq_true, decide_eq_true_eq]
        split
        · exact absurd ‹_› hgo
        · rfl
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      rcases h1 c hc with ⟨hm, hok⟩ | hc'
      · exact .inl ⟨List.mem_cons_of_mem _ hm, hok⟩
      · rcases hsplit with ⟨h, hok⟩ | h
        · rw [h] at hc'
          cases hc'
          exact .inl ⟨List.mem_cons_self, hok⟩
        · rw [h] at hc'
          exact .inr hc'
    · intro s hs hok
      rcases List.mem_cons.mp hs with rfl | hs
      · obtain ⟨c, hc, hsc⟩ := hself hok
        obtain ⟨c', hc', hcc⟩ := h3 c hc
        exact ⟨c', hc', Nat.le_trans hsc hcc⟩
      · exact h2 s hs hok
    · intro c hc
      obtain ⟨c1, hc1, hle1⟩ := hinitNext c hc
      obtain ⟨c2, hc2, hle2⟩ := h3 c1 hc1
      exact ⟨c2, hc2, Nat.le_trans hle1 hle2⟩

private theorem xrefs_functionOf_eq (index : Index) (address : Nat) :
    functionOf index address = index.functions.foldl
      (xrefs_pick fun symbol => spans symbol (nearestStart index address) address) none := rfl

private theorem xrefs_nearest_fold (address : Nat) (symbols : List Bap.Image.Symbol)
    (init : Option Bap.Image.Symbol) :
    symbols.foldl (fun best (symbol : Bap.Image.Symbol) =>
        if symbol.addr ≤ address && best.all (· ≤ symbol.addr) then some symbol.addr else best)
      (init.map Bap.Image.Symbol.addr) =
      (symbols.foldl (xrefs_pick fun symbol => decide (symbol.addr ≤ address)) init).map
        Bap.Image.Symbol.addr := by
  induction symbols generalizing init with
  | nil => rfl
  | cons symbol rest ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    cases init <;> simp [xrefs_pick] <;> split <;> simp

/-- `nearestStart` is the highest start at or below the address, when one exists. -/
private theorem xrefs_nearestStart_spec (index : Index) (address : Nat) :
    (∀ n, nearestStart index address = some n →
      n ≤ address ∧ ∀ s ∈ index.functions, s.addr ≤ address → s.addr ≤ n) ∧
    (∀ s ∈ index.functions, s.addr ≤ address → (nearestStart index address).isSome) := by
  have hnear : nearestStart index address =
      (index.functions.foldl (xrefs_pick fun symbol => decide (symbol.addr ≤ address)) none).map
        Bap.Image.Symbol.addr := xrefs_nearest_fold address index.functions none
  obtain ⟨h1, h2, _⟩ := xrefs_pick_fold (fun symbol => decide (symbol.addr ≤ address)) index.functions none
  constructor
  · intro n hn
    rw [hnear] at hn
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hn
    refine ⟨?_, fun s hs hle => ?_⟩
    · rcases h1 c hc with ⟨_, hok⟩ | h
      · simpa using hok
      · simp at h
    · obtain ⟨c', hc', hle'⟩ := h2 s hs (by simpa using hle)
      rw [hc] at hc'
      cases hc'
      exact hle'
  · intro s hs hle
    rw [hnear]
    obtain ⟨c', hc', _⟩ := h2 s hs (by simpa using hle)
    simp [hc']

/-- `functionOf` returns a known function that spans the address. -/
theorem xrefs_functionOf_spans {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (h : functionOf index address = some symbol) :
    symbol ∈ index.functions ∧ spans symbol (nearestStart index address) address = true := by
  rw [xrefs_functionOf_eq] at h
  rcases (xrefs_pick_fold _ index.functions none).1 symbol h with h | h
  · exact h
  · simp at h

/-- What spanning means: starting at or below the address and, if sized, ending after it; or if
unsized, being the highest start at or below the address. -/
theorem xrefs_spans_iff {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (hmem : symbol ∈ index.functions) :
    spans symbol (nearestStart index address) address = true ↔
      symbol.addr ≤ address ∧
        (if symbol.size = 0 then ∀ s ∈ index.functions, s.addr ≤ address → s.addr ≤ symbol.addr
         else address < symbol.addr + symbol.size) := by
  obtain ⟨h1, h2⟩ := xrefs_nearestStart_spec index address
  simp only [spans, Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro hle
  by_cases hz : symbol.size = 0
  · simp only [hz, ite_true, decide_eq_true_eq]
    constructor
    · intro hn s hs hsle
      exact (h1 _ hn).2 s hs hsle
    · intro hmax
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h2 symbol hmem hle)
      obtain ⟨hna, hall⟩ := h1 n hn
      -- `n` is itself a start at or below the address, hence below `symbol`.
      have hsym := hall symbol hmem hle
      have hnle : n ≤ symbol.addr := by
        have hnear : nearestStart index address =
            (index.functions.foldl (xrefs_pick fun s => decide (s.addr ≤ address)) none).map
              Bap.Image.Symbol.addr := xrefs_nearest_fold address index.functions none
        rw [hnear] at hn
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hn
        rcases (xrefs_pick_fold (fun s => decide (s.addr ≤ address)) index.functions none).1 c hc with
          ⟨hm, _⟩ | h
        · exact hmax c hm hna
        · simp at h
      rw [hn]
      have : n = symbol.addr := by omega
      simp [this]
  · simp [hz]

/-- `functionOf` returns a known function that starts at or below the address. -/
theorem xrefs_functionOf_sound {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (h : functionOf index address = some symbol) :
    symbol ∈ index.functions ∧ symbol.addr ≤ address := by
  obtain ⟨hm, hs⟩ := xrefs_functionOf_spans h
  exact ⟨hm, ((xrefs_spans_iff hm).mp hs).1⟩

/-- No function spanning the address starts after the one `functionOf` returns. -/
theorem xrefs_functionOf_maximal {index : Index} {address : Nat} {symbol other : Bap.Image.Symbol}
    (h : functionOf index address = some symbol) (hother : other ∈ index.functions)
    (hspans : spans other (nearestStart index address) address = true) : other.addr ≤ symbol.addr := by
  rw [xrefs_functionOf_eq] at h
  obtain ⟨c, hc, hsc⟩ := (xrefs_pick_fold (fun s => spans s (nearestStart index address) address)
    index.functions none).2.1 other hother hspans
  rw [h] at hc
  cases hc
  exact hsc

theorem xrefs_functionOf_isSome_iff (index : Index) (address : Nat) :
    (functionOf index address).isSome ↔
      ∃ symbol ∈ index.functions, spans symbol (nearestStart index address) address = true := by
  constructor
  · intro h
    obtain ⟨symbol, hs⟩ := Option.isSome_iff_exists.mp h
    exact ⟨symbol, xrefs_functionOf_spans hs⟩
  · rintro ⟨symbol, hs, hspans⟩
    rw [xrefs_functionOf_eq]
    obtain ⟨c, hc, _⟩ := (xrefs_pick_fold (fun s => spans s (nearestStart index address) address)
      index.functions none).2.1 symbol hs hspans
    exact Option.isSome_iff_exists.mpr ⟨c, hc⟩

/-- A function of known size is never the owner of an address at or past its end. -/
theorem xrefs_functionOf_respects_size {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (hsize : symbol.size ≠ 0) (hpast : symbol.addr + symbol.size ≤ address) :
    functionOf index address ≠ some symbol := by
  intro h
  obtain ⟨hm, hs⟩ := xrefs_functionOf_spans h
  have := ((xrefs_spans_iff hm).mp hs).2
  simp only [hsize, ite_false] at this
  omega

/-- An unsized function ends where the next one starts, so it never owns an address beyond it. -/
theorem xrefs_functionOf_unsized_ends_at_next {index : Index} {address : Nat}
    {symbol next : Bap.Image.Symbol} (hsize : symbol.size = 0) (hnext : next ∈ index.functions)
    (hafter : symbol.addr < next.addr) (hle : next.addr ≤ address) :
    functionOf index address ≠ some symbol := by
  intro h
  obtain ⟨hm, hs⟩ := xrefs_functionOf_spans h
  have := ((xrefs_spans_iff hm).mp hs).2
  simp only [hsize, ite_true] at this
  have := this next hnext hle
  omega

theorem xrefs_owns_iff (index : Index) (symbol : Bap.Image.Symbol) (address : Nat) :
    owns index symbol address = true ↔
      spans symbol (nearestStart index address) address = true ∧
        ∃ owner, functionOf index address = some owner ∧ owner.addr = symbol.addr := by
  simp [owns, Option.any_eq_true]

/-- The function `functionOf` picks owns the address. -/
theorem xrefs_owns_of_functionOf {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (h : functionOf index address = some symbol) : owns index symbol address = true :=
  (xrefs_owns_iff _ _ _).mpr ⟨(xrefs_functionOf_spans h).2, symbol, h, rfl⟩

/-- Owners of one address start at the same place: only aliases can share an instruction. -/
theorem xrefs_owns_unique {index : Index} {address : Nat} {left right : Bap.Image.Symbol}
    (hleft : owns index left address = true) (hright : owns index right address = true) :
    left.addr = right.addr := by
  obtain ⟨_, ownerL, hL, hLeq⟩ := (xrefs_owns_iff _ _ _).mp hleft
  obtain ⟨_, ownerR, hR, hReq⟩ := (xrefs_owns_iff _ _ _).mp hright
  rw [hL] at hR
  cases hR
  omega

/-- Aliases that both span an address own it together, whichever one `functionOf` picked, unless
a more deeply nested function spans it too. -/
theorem xrefs_aliases_both_own {index : Index} {address : Nat} {left right : Bap.Image.Symbol}
    (hleft : left ∈ index.functions) (halias : left.addr = right.addr)
    (hspansL : spans left (nearestStart index address) address = true)
    (hspansR : spans right (nearestStart index address) address = true)
    (hinner : ∀ other ∈ index.functions, spans other (nearestStart index address) address = true →
      other.addr ≤ left.addr) :
    owns index left address = true ∧ owns index right address = true := by
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp
    ((xrefs_functionOf_isSome_iff index address).mpr ⟨left, hleft, hspansL⟩)
  have h1 := xrefs_functionOf_maximal howner hleft hspansL
  obtain ⟨hm, hs⟩ := xrefs_functionOf_spans howner
  have h2 := hinner owner hm hs
  have heq : owner.addr = left.addr := by omega
  exact ⟨(xrefs_owns_iff _ _ _).mpr ⟨hspansL, owner, howner, heq⟩,
    (xrefs_owns_iff _ _ _).mpr ⟨hspansR, owner, howner, heq.trans halias⟩⟩

/-- Callees are found through any name of the owning function. -/
theorem xrefs_mem_callees_iff (index : Index) (function : String) (xref : Xref) :
    xref ∈ callees index function ↔ xref ∈ index.xrefs ∧ xref.kind = .call ∧
      ∃ symbol ∈ index.functions, symbol.name = function ∧ owns index symbol xref.source = true := by
  simp [callees]

theorem xrefs_functionAt_sound {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (h : functionAt index address = some symbol) :
    symbol ∈ index.functions ∧ symbol.addr = address := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem xrefs_functionAt_isSome_iff (index : Index) (address : Nat) :
    (functionAt index address).isSome ↔ ∃ symbol ∈ index.functions, symbol.addr = address := by
  simp [functionAt, List.find?_isSome]

/-- A function starting exactly at an address is what `functionOf` picks, up to start address. -/
theorem xrefs_functionOf_of_functionAt {index : Index} {address : Nat} {symbol : Bap.Image.Symbol}
    (h : functionAt index address = some symbol) :
    ∃ owner, functionOf index address = some owner ∧ owner.addr = address := by
  obtain ⟨hs, heq⟩ := xrefs_functionAt_sound h
  have hspans : spans symbol (nearestStart index address) address = true := by
    rw [xrefs_spans_iff hs]
    refine ⟨Nat.le_of_eq heq, ?_⟩
    split
    · intro s _ hle
      omega
    · omega
  obtain ⟨owner, howner⟩ := Option.isSome_iff_exists.mp
    ((xrefs_functionOf_isSome_iff index address).mpr ⟨symbol, hs, hspans⟩)
  refine ⟨owner, howner, ?_⟩
  have h1 := (xrefs_functionOf_sound howner).2
  have h2 := xrefs_functionOf_maximal howner hs hspans
  omega

end Xrefs

section Callgraph
open Bap.Analysis.Callgraph
open_private Bap.Graph.Basic in Bap.Graph : closure closureStep

theorem callgraph_eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.Nodup := by
  generalize hn : values.length = n
  induction n using Nat.strongRecOn generalizing values with
  | _ n ih =>
    cases values with
    | nil => simp
    | cons head tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups]
      · have hlen : (tail.filter fun b => !b == head).length ≤ tail.length := List.length_filter_le _ _
        simp only [List.length_cons] at hn
        exact ih _ (by omega) _ rfl

theorem callgraph_mem_nodes_iff (index : Bap.Analysis.Xrefs.Index) (node : Nat) :
    node ∈ (create index).graph.nodes ↔
      (∃ symbol ∈ index.functions, symbol.addr = node) ∨
        ∃ xref ∈ index.xrefs, xref.kind = .call ∧ xref.target = node := by
  simp only [create, List.mem_eraseDups, List.mem_append, List.mem_map, List.mem_filterMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨xref, hx, hk⟩
    cases hkind : xref.kind <;> simp [hkind] at hk
    exact ⟨xref, hx, hkind, hk⟩
  · rintro ⟨xref, hx, hk, ht⟩
    exact ⟨xref, hx, by simp [hk, ht]⟩

/-- An edge exists exactly for a call reference, from the function that owns the call site. -/
theorem callgraph_mem_edges_iff (index : Bap.Analysis.Xrefs.Index) (caller callee : Nat) :
    (caller, callee) ∈ (create index).graph.edges ↔
      ∃ xref ∈ index.xrefs, xref.kind = .call ∧ xref.target = callee ∧
        ∃ owner, Bap.Analysis.Xrefs.functionOf index xref.source = some owner ∧ owner.addr = caller := by
  simp only [create, List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨xref, hx, h⟩
    by_cases hk : xref.kind = .call
    · simp [hk] at h
      obtain ⟨owner, ho, h1, h2⟩ := h
      exact ⟨xref, hx, hk, h2, owner, ho, h1⟩
    · simp [hk] at h
  · rintro ⟨xref, hx, hk, ht, owner, ho, ha⟩
    exact ⟨xref, hx, by simp [hk, ho, ha, ht]⟩

theorem callgraph_nodes_nodup (index : Bap.Analysis.Xrefs.Index) :
    (create index).graph.nodes.Nodup := callgraph_eraseDups_nodup _

theorem callgraph_edges_nodup (index : Bap.Analysis.Xrefs.Index) :
    (create index).graph.edges.Nodup := callgraph_eraseDups_nodup _

/-- Both endpoints of every call-graph edge are nodes, and the caller is a known function. -/
theorem callgraph_edge_endpoints {index : Bap.Analysis.Xrefs.Index} {caller callee : Nat}
    (h : (caller, callee) ∈ (create index).graph.edges) :
    caller ∈ (create index).graph.nodes ∧ callee ∈ (create index).graph.nodes ∧
      ∃ symbol ∈ index.functions, symbol.addr = caller := by
  obtain ⟨xref, hx, hk, ht, owner, ho, ha⟩ := (callgraph_mem_edges_iff index caller callee).mp h
  have hown := (Bap.Proofs.Analysis.xrefs_functionOf_sound ho).1
  refine ⟨(callgraph_mem_nodes_iff index caller).mpr (.inl ⟨owner, hown, ha⟩),
    (callgraph_mem_nodes_iff index callee).mpr (.inr ⟨xref, hx, hk, ht⟩), owner, hown, ha⟩

/-- Reachability along edges from a set of roots that are graph nodes. -/
inductive callgraph_Path (graph : Bap.Graph.Graph Nat) (roots : List Nat) : Nat → Prop where
  | root {node} : node ∈ roots → node ∈ graph.nodes → callgraph_Path graph roots node
  | step {source target} : callgraph_Path graph roots source → (source, target) ∈ graph.edges →
      target ∈ graph.nodes → callgraph_Path graph roots target

private theorem callgraph_mem_step {graph : Bap.Graph.Graph Nat} {seen : List Nat} {node : Nat} :
    node ∈ closureStep graph seen ↔ node ∈ seen ∨
      (node ∈ graph.nodes ∧ node ∉ seen ∧ ∃ pred, (pred, node) ∈ graph.edges ∧ pred ∈ seen) := by
  simp only [closureStep, List.mem_append, List.mem_filter]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  rw [decide_eq_true_iff]
  apply and_congr Iff.rfl
  simp [Bap.Graph.predecessors]

private theorem callgraph_filter_length_lt {l : List Nat} {p q : Nat → Bool}
    (hqp : ∀ x, q x = true → p x = true) {x : Nat} (hx : x ∈ l) (hp : p x = true) (hq : q x = false) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons head tail ih =>
    have hle : (tail.filter q).length ≤ (tail.filter p).length := by
      apply List.Sublist.length_le
      exact List.Sublist.trans (by
        have : tail.filter q = (tail.filter p).filter q := by
          rw [List.filter_filter]
          congr 1
          funext a
          cases hqa : q a with
          | false => simp
          | true => simp [hqp a hqa]
        rw [this]
        exact List.filter_sublist) (List.Sublist.refl _)
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hp, hq]; omega
    · have := ih hx
      by_cases hqh : q head = true
      · simp [hqh, hqp head hqh]; omega
      · by_cases hph : p head = true
        · simp [hqh, hph]; omega
        · simp [hqh, hph]; omega

private theorem callgraph_closure_props (graph : Bap.Graph.Graph Nat) (roots : List Nat) :
    ∀ (fuel : Nat) (seen : List Nat),
      (∀ n ∈ seen, callgraph_Path graph roots n) →
      (∀ n ∈ seen, n ∈ closure graph fuel seen) ∧
      (∀ n ∈ closure graph fuel seen, callgraph_Path graph roots n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen h
    exact ⟨fun _ hn => hn, h⟩
  | succ fuel ih =>
    intro seen h
    simp only [closure]
    split
    · exact ⟨fun _ hn => hn, h⟩
    · have hnext : ∀ n ∈ closureStep graph seen, callgraph_Path graph roots n := by
        intro n hn
        rcases callgraph_mem_step.mp hn with hn | ⟨hnode, _, pred, he, hp⟩
        · exact h n hn
        · exact .step (h pred hp) he hnode
      obtain ⟨h1, h2⟩ := ih _ hnext
      refine ⟨fun n hn => h1 n (callgraph_mem_step.mpr (.inl hn)), h2⟩

private theorem callgraph_closure_closed (graph : Bap.Graph.Graph Nat) :
    ∀ (fuel : Nat) (seen : List Nat),
      (graph.nodes.filter fun n => decide (n ∉ seen)).length < fuel →
      ∀ source target, source ∈ closure graph fuel seen → (source, target) ∈ graph.edges →
        target ∈ graph.nodes → target ∈ closure graph fuel seen := by
  intro fuel
  induction fuel with
  | zero => intro seen h; omega
  | succ fuel ih =>
    intro seen hfuel source target hs he ht
    simp only [closure] at hs ⊢
    split at hs
    · rename_i heq
      simp only [heq, ite_true]
      refine Classical.byContradiction fun hnot => ?_
      have : target ∈ closureStep graph seen :=
        callgraph_mem_step.mpr (.inr ⟨ht, hnot, source, he, hs⟩)
      rw [heq] at this
      exact hnot this
    · rename_i hne
      simp only [hne, ite_false]
      refine ih _ ?_ source target hs he ht
      have hexists : ∃ x, x ∈ closureStep graph seen ∧ x ∉ seen := by
        refine Classical.byContradiction fun hall => ?_
        apply hne
        simp only [closureStep]
        have : (graph.nodes.filter fun node => decide (node ∉ seen ∧
            (Bap.Graph.predecessors graph node).any fun pred => decide (pred ∈ seen))) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          apply hall
          have hdec := (List.mem_filter.mp hx).2
          refine ⟨x, ?_, (decide_eq_true_iff.mp hdec).1⟩
          simp only [closureStep, List.mem_append]
          exact .inr hx
        rw [this, List.append_nil]
      obtain ⟨x, hx, hxs⟩ := hexists
      have hxn : x ∈ graph.nodes := by
        rcases callgraph_mem_step.mp hx with h | ⟨h, _⟩
        · exact absurd h hxs
        · exact h
      have hlt : (graph.nodes.filter fun n => decide (n ∉ closureStep graph seen)).length <
          (graph.nodes.filter fun n => decide (n ∉ seen)).length := by
        apply callgraph_filter_length_lt (x := x) _ hxn (by simpa using hxs) (by simpa using hx)
        intro y hy
        simp only [decide_eq_true_eq] at hy ⊢
        exact fun hmem => hy (callgraph_mem_step.mpr (.inl hmem))
      omega

theorem callgraph_mem_reachableFrom_iff (graph : Bap.Graph.Graph Nat) (roots : List Nat) (node : Nat) :
    node ∈ Bap.Graph.reachableFrom graph roots ↔ callgraph_Path graph roots node := by
  simp only [Bap.Graph.reachableFrom]
  have hseeds : ∀ n ∈ (roots.filter fun node => decide (node ∈ graph.nodes)).eraseDups,
      callgraph_Path graph roots n := by
    intro n hn
    simp only [List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at hn
    exact .root hn.1 hn.2
  obtain ⟨hmono, hsound⟩ := callgraph_closure_props graph roots (graph.nodes.length + 1) _ hseeds
  refine ⟨hsound node, fun h => ?_⟩
  induction h with
  | root hr hn =>
    exact hmono _ (by simp only [List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]; exact ⟨hr, hn⟩)
  | step _ he ht ih =>
    refine callgraph_closure_closed graph _ _ ?_ _ _ ih he ht
    exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A node is reachable exactly when an edge path connects it to a root that is a node. -/
theorem callgraph_mem_reachable_iff (callgraph : Callgraph) (roots : List Nat) (node : Nat) :
    node ∈ reachable callgraph roots ↔ callgraph_Path callgraph.graph roots node :=
  callgraph_mem_reachableFrom_iff _ _ _

theorem callgraph_reachable_subset_nodes {callgraph : Callgraph} {roots : List Nat} {node : Nat}
    (h : node ∈ reachable callgraph roots) : node ∈ callgraph.graph.nodes := by
  have := (callgraph_mem_reachable_iff _ _ _).mp h
  cases this with
  | root _ hn => exact hn
  | step _ _ hn => exact hn

theorem callgraph_root_mem_reachable {callgraph : Callgraph} {roots : List Nat} {root : Nat}
    (hr : root ∈ roots) (hn : root ∈ callgraph.graph.nodes) : root ∈ reachable callgraph roots :=
  (callgraph_mem_reachable_iff _ _ _).mpr (.root hr hn)

/-- In a created call graph, reachability is closed under calls without any node side condition. -/
theorem callgraph_reachable_closed {index : Bap.Analysis.Xrefs.Index} {roots : List Nat}
    {caller callee : Nat} (hc : caller ∈ reachable (create index) roots)
    (he : (caller, callee) ∈ (create index).graph.edges) : callee ∈ reachable (create index) roots :=
  (callgraph_mem_reachable_iff _ _ _).mpr
    (.step ((callgraph_mem_reachable_iff _ _ _).mp hc) he (callgraph_edge_endpoints he).2.1)

theorem callgraph_recursive_subset_nodes {callgraph : Callgraph} {node : Nat}
    (h : node ∈ recursiveFunctions callgraph) : node ∈ callgraph.graph.nodes := by
  simp only [recursiveFunctions, List.mem_filter] at h
  exact h.1

theorem callgraph_self_loop_recursive {callgraph : Callgraph} {node : Nat}
    (hn : node ∈ callgraph.graph.nodes) (he : (node, node) ∈ callgraph.graph.edges) :
    node ∈ recursiveFunctions callgraph := by
  simp only [recursiveFunctions, List.mem_filter, Bool.or_eq_true]
  exact ⟨hn, .inr (by simpa using he)⟩

end Callgraph

section Strings
open Bap.Analysis.Strings
open_private Bap.Analysis.Strings in Bap.Analysis.Strings : printable finish scanAscii pairs decodePair scanUtf16

/-- An ASCII result: long enough, and exactly the printable run at its address in `bytes`. -/
def strings_AsciiLocated (minimum base : Nat) (bytes : List UInt8) (result : Nat × String) : Prop :=
  minimum ≤ result.2.length ∧ ∃ before run after,
    bytes = before ++ run ++ after ∧ result.1 = base + before.length ∧
    run.all (fun byte => 0x20 ≤ byte.toNat && byte.toNat ≤ 0x7e) = true ∧
    result.2.toList = run.map fun byte => Char.ofNat byte.toNat

theorem strings_finish_mem {minimum width next : Nat} {chars : List Char} {results : List (Nat × String)}
    {result : Nat × String} (h : result ∈ finish minimum width next chars results) :
    result ∈ results ∨ (chars.length ≥ minimum ∧ result = (next - chars.length * width, String.ofList chars)) := by
  simp only [finish] at h
  split at h
  · rcases List.mem_cons.mp h with h | h
    · exact .inr ⟨by assumption, h⟩
    · exact .inl h
  · exact .inl h

private theorem strings_scanAscii_located (minimum base : Nat) (seen : List UInt8) (run : List UInt8)
    (rest : List UInt8) (results : List (Nat × String))
    (hresults : ∀ r ∈ results, strings_AsciiLocated minimum base (seen ++ run ++ rest) r)
    (hrun : run.all (fun byte => 0x20 ≤ byte.toNat && byte.toNat ≤ 0x7e) = true) :
    ∀ r ∈ scanAscii minimum (base + seen.length + run.length)
        (run.map fun byte => Char.ofNat byte.toNat) results rest,
      strings_AsciiLocated minimum base (seen ++ run ++ rest) r := by
  induction rest generalizing seen run results with
  | nil =>
    intro r hr
    simp only [scanAscii, List.mem_reverse] at hr
    rcases strings_finish_mem hr with h | ⟨hlen, rfl⟩
    · exact hresults r h
    · simp only [List.length_map, Nat.mul_one, List.append_nil] at hlen ⊢
      refine ⟨by simpa using hlen, seen, run, [], by simp, by simp, hrun, by simp⟩
  | cons byte rest ih =>
    intro r hr
    simp only [scanAscii] at hr
    split at hr
    · rename_i hp
      have hnew := ih seen (run ++ [byte]) results (by simpa using hresults)
        (by simpa [printable] using ⟨by simpa using hrun, by simpa [printable] using hp⟩)
      have hnext : base + seen.length + (run ++ [byte]).length = base + seen.length + run.length + 1 := by
        simp; omega
      simp only [hnext, List.map_append, List.map_cons, List.map_nil] at hnew
      simpa using hnew r hr
    · have hnew := ih (seen ++ run ++ [byte]) [] (finish minimum 1 (base + seen.length + run.length)
        (run.map fun byte => Char.ofNat byte.toNat) results) (by
          intro r hr
          simp only [List.append_assoc, List.singleton_append] at *
          rcases strings_finish_mem hr with h | ⟨hlen, rfl⟩
          · simpa using hresults r h
          · simp only [List.length_map, Nat.mul_one] at hlen ⊢
            exact ⟨by simpa using hlen, seen, run, byte :: rest, by simp, by simp, hrun, by simp⟩)
        (by simp)
      have hnext : base + (seen ++ run ++ [byte]).length + ([] : List UInt8).length =
          base + seen.length + run.length + 1 := by simp; omega
      simp only [hnext, List.map_nil, List.append_nil] at hnew
      simpa using hnew r hr

/-- Every ASCII scan result is long enough, printable, and is exactly the bytes at its address. -/
theorem strings_scanAscii_sound (minimum base : Nat) (bytes : List UInt8) :
    ∀ r ∈ scanAscii minimum base [] [] bytes, strings_AsciiLocated minimum base bytes r := by
  have := strings_scanAscii_located minimum base [] [] bytes [] (by simp) (by simp)
  simpa using this

/-- Input that is entirely printable and long enough is one single result. -/
theorem strings_scanAscii_all_printable (minimum base : Nat) (bytes : List UInt8)
    (hall : ∀ byte ∈ bytes, 0x20 ≤ byte.toNat ∧ byte.toNat ≤ 0x7e) (hlen : minimum ≤ bytes.length) :
    scanAscii minimum base [] [] bytes =
      [(base, String.ofList (bytes.map fun byte => Char.ofNat byte.toNat))] := by
  have key : ∀ (run rest : List UInt8), (∀ byte ∈ rest, 0x20 ≤ byte.toNat ∧ byte.toNat ≤ 0x7e) →
      minimum ≤ run.length + rest.length →
      scanAscii minimum (base + run.length) (run.map fun byte => Char.ofNat byte.toNat) [] rest =
        [(base, String.ofList ((run ++ rest).map fun byte => Char.ofNat byte.toNat))] := by
    intro run rest
    induction rest generalizing run with
    | nil =>
      intro _ hmin
      simp only [scanAscii, finish, List.length_map, Nat.mul_one]
      have hm : run.length ≥ minimum := by simpa using hmin
      simp [hm]
    | cons byte rest ih =>
      intro hprint hmin
      have hb := hprint byte List.mem_cons_self
      have hp : printable byte = true := by simp [printable, hb.1, hb.2]
      simp only [scanAscii, hp, ite_true]
      have := ih (run ++ [byte]) (fun b hb => hprint b (List.mem_cons_of_mem _ hb))
        (by simp at hmin ⊢; omega)
      simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append] at this
      simpa [Nat.add_assoc] using this
  simpa using key [] bytes hall (by simpa using hlen)

theorem strings_pairs_flatten (bytes : List UInt8) :
    ∃ tail, bytes = (pairs bytes).flatMap (fun pair => [pair.1, pair.2]) ++ tail ∧ tail.length ≤ 1 := by
  generalize hn : bytes.length = n
  induction n using Nat.strongRecOn generalizing bytes with
  | _ n ih =>
    match bytes, hn with
    | [], _ => exact ⟨[], by simp [pairs], by simp⟩
    | [x], _ => exact ⟨[x], by simp [pairs], by simp⟩
    | x :: y :: rest, hn =>
      obtain ⟨tail, ht, hl⟩ := ih rest.length (by simp at hn; omega) rest rfl
      refine ⟨tail, ?_, hl⟩
      simp only [pairs, List.flatMap_cons, List.cons_append, List.nil_append]
      rw [← ht]

/-- The code byte and the byte that must be zero, for either byte order. -/
def strings_codeUnit (little : Bool) (unit : UInt8 × UInt8) : UInt8 × UInt8 :=
  if little then (unit.1, unit.2) else (unit.2, unit.1)

theorem strings_decodePair_eq_some (little : Bool) (first second : UInt8) (char : Char) :
    decodePair little first second = some char ↔
      (strings_codeUnit little (first, second)).2 = 0 ∧
      printable (strings_codeUnit little (first, second)).1 = true ∧
      char = Char.ofNat (strings_codeUnit little (first, second)).1.toNat := by
  cases little
  · by_cases h0 : first = 0 <;> by_cases hp : printable second = true <;>
      simp [decodePair, strings_codeUnit, h0, hp, eq_comm (a := char)]
  · by_cases h0 : second = 0 <;> by_cases hp : printable first = true <;>
      simp [decodePair, strings_codeUnit, h0, hp, eq_comm (a := char)]

/-- A UTF-16 result over code units: long enough, printable with a zero high byte, and at an
address that counts the preceding units in bytes. -/
def strings_UnitsLocated (minimum : Nat) (little : Bool) (base : Nat) (units : List (UInt8 × UInt8))
    (result : Nat × String) : Prop :=
  minimum ≤ result.2.length ∧ ∃ before run after,
    units = before ++ run ++ after ∧ result.1 = base + 2 * before.length ∧
    (∀ unit ∈ run, (strings_codeUnit little unit).2 = 0 ∧ printable (strings_codeUnit little unit).1 = true) ∧
    result.2.toList = run.map fun unit => Char.ofNat (strings_codeUnit little unit).1.toNat

private theorem strings_scanUtf16_located (minimum : Nat) (little : Bool) (base : Nat)
    (seen run rest : List (UInt8 × UInt8)) (results : List (Nat × String))
    (hresults : ∀ r ∈ results, strings_UnitsLocated minimum little base (seen ++ run ++ rest) r)
    (hrun : ∀ unit ∈ run, (strings_codeUnit little unit).2 = 0 ∧ printable (strings_codeUnit little unit).1 = true) :
    ∀ r ∈ scanUtf16 minimum little (base + 2 * seen.length + 2 * run.length)
        (run.map fun unit => Char.ofNat (strings_codeUnit little unit).1.toNat) results rest,
      strings_UnitsLocated minimum little base (seen ++ run ++ rest) r := by
  induction rest generalizing seen run results with
  | nil =>
    intro r hr
    simp only [scanUtf16, List.mem_reverse] at hr
    rcases strings_finish_mem hr with h | ⟨hlen, rfl⟩
    · exact hresults r h
    · simp only [List.length_map] at hlen ⊢
      refine ⟨by simpa using hlen, seen, run, [], by simp, ?_, hrun, by simp⟩
      simp only
      omega
  | cons unit rest ih =>
    obtain ⟨first, second⟩ := unit
    intro r hr
    simp only [scanUtf16] at hr
    cases hdecode : decodePair little first second with
    | some char =>
      obtain ⟨h0, hp, hc⟩ := (strings_decodePair_eq_some little first second char).mp hdecode
      rw [hdecode] at hr
      have hnew := ih seen (run ++ [(first, second)]) results (by simpa using hresults)
        (by
          intro unit hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hrun unit hu
          · simp only [List.mem_singleton] at hu
            subst hu
            exact ⟨h0, hp⟩)
      have hnext : base + 2 * seen.length + 2 * (run ++ [(first, second)]).length =
          base + 2 * seen.length + 2 * run.length + 2 := by simp; omega
      simp only [hnext, List.map_append, List.map_cons, List.map_nil] at hnew
      have := hnew r (by rw [← hc]; exact hr)
      simpa using this
    | none =>
      rw [hdecode] at hr
      have hnew := ih (seen ++ run ++ [(first, second)]) [] (finish minimum 2 (base + 2 * seen.length + 2 * run.length)
        (run.map fun unit => Char.ofNat (strings_codeUnit little unit).1.toNat) results) (by
          intro r hr
          simp only [List.append_assoc, List.singleton_append] at *
          rcases strings_finish_mem hr with h | ⟨hlen, rfl⟩
          · simpa using hresults r h
          · simp only [List.length_map] at hlen ⊢
            refine ⟨by simpa using hlen, seen, run, (first, second) :: rest, by simp, ?_, hrun, by simp⟩
            simp only
            omega)
        (by simp)
      have hnext : base + 2 * (seen ++ run ++ [(first, second)]).length + 2 * ([] : List (UInt8 × UInt8)).length =
          base + 2 * seen.length + 2 * run.length + 2 := by simp; omega
      simp only [hnext, List.map_nil, List.append_nil] at hnew
      simpa using hnew r hr

theorem strings_scanUtf16_sound (minimum : Nat) (little : Bool) (base : Nat) (units : List (UInt8 × UInt8)) :
    ∀ r ∈ scanUtf16 minimum little base [] [] units, strings_UnitsLocated minimum little base units r := by
  have := strings_scanUtf16_located minimum little base [] [] units [] (by simp) (by simp)
  simpa using this

/-- A UTF-16 result in raw bytes: each code unit sits at an even offset from the region start. -/
def strings_Utf16Located (minimum : Nat) (little : Bool) (base : Nat) (bytes : List UInt8)
    (result : Nat × String) : Prop :=
  minimum ≤ result.2.length ∧ ∃ (before : List UInt8) (run : List (UInt8 × UInt8)) (after : List UInt8),
    bytes = before ++ run.flatMap (fun unit => [unit.1, unit.2]) ++ after ∧
    2 ∣ before.length ∧ result.1 = base + before.length ∧
    (∀ unit ∈ run, (strings_codeUnit little unit).2 = 0 ∧
      0x20 ≤ (strings_codeUnit little unit).1.toNat ∧ (strings_codeUnit little unit).1.toNat ≤ 0x7e) ∧
    result.2.toList = run.map fun unit => Char.ofNat (strings_codeUnit little unit).1.toNat

private theorem strings_flatten_length (units : List (UInt8 × UInt8)) :
    (units.flatMap fun unit => [unit.1, unit.2]).length = 2 * units.length := by
  induction units with
  | nil => simp
  | cons head tail ih => simp [ih]; omega

theorem strings_scanUtf16_bytes_sound (minimum : Nat) (little : Bool) (base : Nat) (bytes : List UInt8) :
    ∀ r ∈ scanUtf16 minimum little base [] [] (pairs bytes), strings_Utf16Located minimum little base bytes r := by
  intro r hr
  obtain ⟨hmin, before, run, after, hunits, haddr, hall, htext⟩ :=
    strings_scanUtf16_sound minimum little base (pairs bytes) r hr
  obtain ⟨tail, htail, _⟩ := strings_pairs_flatten bytes
  refine ⟨hmin, before.flatMap (fun unit => [unit.1, unit.2]), run,
    after.flatMap (fun unit => [unit.1, unit.2]) ++ tail, ?_, ?_, ?_, ?_, htext⟩
  · conv => lhs; rw [htail, hunits]
    simp [List.flatMap_append]
  · rw [strings_flatten_length]
    exact ⟨_, rfl⟩
  · rw [strings_flatten_length, haddr]
  · intro unit hu
    obtain ⟨h0, hp⟩ := hall unit hu
    simpa [printable] using And.intro h0 hp

/-- Soundness of whole-image string extraction: every record is long enough, printable, and made
of exactly the bytes of one memory region at the record's address, in the record's encoding. -/
theorem strings_strings_sound (image : Bap.Image.Image) (minimum : Nat) (record : StringRecord)
    (h : record ∈ strings image minimum) :
    ∃ entry ∈ image.memory.entries,
      (record.encoding = .ascii ∧
        strings_AsciiLocated minimum entry.1.addr entry.1.data.toList (record.address, record.text)) ∨
      (record.encoding = .utf16le ∧
        strings_Utf16Located minimum true entry.1.addr entry.1.data.toList (record.address, record.text)) ∨
      (record.encoding = .utf16be ∧
        strings_Utf16Located minimum false entry.1.addr entry.1.data.toList (record.address, record.text)) := by
  simp only [strings, List.mem_flatMap, List.mem_append, List.mem_map] at h
  obtain ⟨entry, he, h⟩ := h
  refine ⟨entry, he, ?_⟩
  rcases h with (⟨result, hr, rfl⟩ | ⟨result, hr, rfl⟩) | ⟨result, hr, rfl⟩
  · exact .inl ⟨rfl, strings_scanAscii_sound _ _ _ _ hr⟩
  · exact .inr (.inl ⟨rfl, strings_scanUtf16_bytes_sound _ _ _ _ _ hr⟩)
  · exact .inr (.inr ⟨rfl, strings_scanUtf16_bytes_sound _ _ _ _ _ hr⟩)

/-- Every extracted character is printable ASCII. -/
theorem strings_char_printable {image : Bap.Image.Image} {minimum : Nat} {record : StringRecord}
    (h : record ∈ strings image minimum) {char : Char} (hc : char ∈ record.text.toList) :
    0x20 ≤ char.toNat ∧ char.toNat ≤ 0x7e := by
  have hbyte : ∀ byte : UInt8, 0x20 ≤ byte.toNat → byte.toNat ≤ 0x7e →
      (Char.ofNat byte.toNat).toNat = byte.toNat := by
    intro byte h1 h2
    have hvalid : Nat.isValidChar byte.toNat := Or.inl (by omega)
    simp only [Char.ofNat, hvalid, dite_true]
    rfl
  obtain ⟨_, _, h⟩ := strings_strings_sound image minimum record h
  rcases h with ⟨_, _, _, run, _, _, _, hall, htext⟩ | ⟨_, _, _, run, _, _, _, _, hall, htext⟩ |
      ⟨_, _, _, run, _, _, _, _, hall, htext⟩
  · simp only at htext
    rw [htext] at hc
    obtain ⟨byte, hb, rfl⟩ := List.mem_map.mp hc
    have := List.all_eq_true.mp hall byte hb
    simp at this
    rw [hbyte byte this.1 this.2]
    exact this
  all_goals
    simp only at htext
    rw [htext] at hc
    obtain ⟨unit, hu, rfl⟩ := List.mem_map.mp hc
    obtain ⟨_, h1, h2⟩ := hall unit hu
    rw [hbyte _ h1 h2]
    exact ⟨h1, h2⟩

end Strings

section Slice
open Bap.Analysis.Slice
open_private Bap.Analysis.Slice in Bap.Analysis.Slice :
  Info Info.mk Info.defs Info.mayDefs Info.uses Info.dynamic Info.always Info.unknownWrite constant
  usesExp merge memoryWrites isStore stmtInfo addUnique removeDefinitions touches relevant
  backwardInstruction linear

/-- The summary of a block of statements. -/
private def slice_block (code : Bap.Bil.Program) : Info :=
  code.foldl (fun info stmt => merge info (stmtInfo stmt)) (Info.mk [] [] [] false false false)

/-- One backward step of the slicer. -/
private def slice_step (current : List Location × List Nat × Bool) (insn : Bap.Disasm.Insn) :
    List Location × List Nat × Bool :=
  if relevant current.1 (slice_block insn.bil) then
    (backwardInstruction current.1 (slice_block insn.bil), current.2.1 ++ [insn.address],
      current.2.2 && !Info.dynamic (slice_block insn.bil))
  else
    current

private theorem slice_backward_eq (instructions : List Bap.Disasm.Insn) (criteria : List Location) :
    backward instructions criteria =
      let final := instructions.reverse.foldl slice_step (criteria, [], true)
      { sites := final.2.1.reverse, live := final.1, complete := final.2.2 } := rfl

theorem slice_covers_overlaps {outer inner : Location} (h : outer.covers inner = true) :
    outer.overlaps inner = true := by
  simp only [Location.covers, Bool.and_eq_true] at h
  exact h.1

theorem slice_overlaps_symm (left right : Location) : left.overlaps right = right.overlaps left := by
  cases left <;> cases right <;> simp only [Location.overlaps]
  · rename_i a b
    by_cases h : a = b
    · subst h
      rfl
    · have h1 : (a == b) = false := by simpa using h
      have h2 : (b == a) = false := by simpa using fun e : b = a => h e.symm
      rw [h1, h2]
  · rw [Bool.and_comm]

/-- Non-empty byte ranges overlap exactly when they share an address. -/
theorem slice_overlaps_mem_iff {left leftSize right rightSize : Nat} (hl : 0 < leftSize)
    (hr : 0 < rightSize) :
    (Location.mem left leftSize).overlaps (.mem right rightSize) = true ↔
      ∃ byte, left ≤ byte ∧ byte < left + leftSize ∧ right ≤ byte ∧ byte < right + rightSize := by
  simp only [Location.overlaps, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    by_cases hle : left ≤ right
    · exact ⟨right, by omega, by omega, by omega, by omega⟩
    · exact ⟨left, by omega, by omega, by omega, by omega⟩
  · rintro ⟨byte, _, _, _, _⟩
    omega

/-- A covering write contains every byte of what it covers. -/
theorem slice_covers_mem {outer outerSize inner innerSize : Nat}
    (h : (Location.mem outer outerSize).covers (.mem inner innerSize) = true) (byte : Nat)
    (hl : inner ≤ byte) (hr : byte < inner + innerSize) :
    outer ≤ byte ∧ byte < outer + outerSize := by
  simp only [Location.covers, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

private theorem slice_relevant_iff (live : List Location) (info : Info) :
    relevant live info = true ↔ Info.always info = true ∨
      (Info.unknownWrite info = true ∧ ∃ loc ∈ live, loc.isMemory = true) ∨
      (∃ d ∈ Info.defs info, ∃ loc ∈ live, d.overlaps loc = true) ∨
      (∃ d ∈ Info.mayDefs info, ∃ loc ∈ live, d.overlaps loc = true) ∨
      (∃ d ∈ Info.uses info, ∃ loc ∈ live, d.overlaps loc = true) := by
  simp [relevant, touches, or_assoc]

private theorem slice_mem_foldl_addUnique (uses live : List Location) (loc : Location) :
    loc ∈ uses.foldl addUnique live ↔ loc ∈ live ∨ loc ∈ uses := by
  induction uses generalizing live with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, ih, addUnique, List.mem_cons]
    split
    · rename_i h
      have : head ∈ live := by simpa using h
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl this
        · exact .inr h
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h

/-- Liveness transfer: a location is live before an instruction when it is used there, or live
after it and not entirely overwritten on every path through it. -/
theorem slice_mem_backwardInstruction (live : List Location) (info : Info) (loc : Location) :
    loc ∈ backwardInstruction live info ↔
      (loc ∈ live ∧ ∀ d ∈ Info.defs info, d.covers loc = false) ∨ loc ∈ Info.uses info := by
  simp [backwardInstruction, slice_mem_foldl_addUnique, removeDefinitions]

/-- Only a must-definition covering the whole location ends its liveness. -/
theorem slice_killed_iff {live : List Location} {info : Info} {loc : Location} (hl : loc ∈ live)
    (hu : loc ∉ Info.uses info) :
    loc ∉ backwardInstruction live info ↔ ∃ d ∈ Info.defs info, d.covers loc = true := by
  rw [slice_mem_backwardInstruction]
  simp [hl, hu]

private theorem slice_usesExp_pure (exp : Bap.Bil.Exp) :
    Info.defs (usesExp exp) = [] ∧ Info.mayDefs (usesExp exp) = [] ∧
      Info.unknownWrite (usesExp exp) = false := by
  induction exp <;> simp_all [usesExp]
  all_goals split <;> simp

private theorem slice_fold_fields (code : Bap.Bil.Program) (init : Info) :
    let result := code.foldl (fun info stmt => merge info (stmtInfo stmt)) init
    Info.defs result = Info.defs init ++ code.flatMap (fun s => Info.defs (stmtInfo s)) ∧
    Info.mayDefs result = Info.mayDefs init ++ code.flatMap (fun s => Info.mayDefs (stmtInfo s)) ∧
    Info.unknownWrite result = (Info.unknownWrite init || code.any fun s => Info.unknownWrite (stmtInfo s)) ∧
    Info.dynamic result = (Info.dynamic init || code.any fun s => Info.dynamic (stmtInfo s)) := by
  induction code generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (merge init (stmtInfo head))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [merge] using h1
    · simpa [merge] using h2
    · simpa [merge, Bool.or_assoc] using h3
    · simpa [merge, Bool.or_assoc] using h4

private theorem slice_block_defs (code : Bap.Bil.Program) (d : Location) :
    d ∈ Info.defs (slice_block code) ↔ ∃ s ∈ code, d ∈ Info.defs (stmtInfo s) := by
  rw [slice_block, (slice_fold_fields code _).1]
  simp

private theorem slice_block_mayDefs (code : Bap.Bil.Program) (d : Location) :
    d ∈ Info.mayDefs (slice_block code) ↔ ∃ s ∈ code, d ∈ Info.mayDefs (stmtInfo s) := by
  rw [slice_block, (slice_fold_fields code _).2.1]
  simp

private theorem slice_block_unknownWrite (code : Bap.Bil.Program) :
    Info.unknownWrite (slice_block code) = true ↔ ∃ s ∈ code, Info.unknownWrite (stmtInfo s) = true := by
  rw [slice_block, (slice_fold_fields code _).2.2.1]
  simp

private theorem slice_block_dynamic (code : Bap.Bil.Program) :
    Info.dynamic (slice_block code) = true ↔ ∃ s ∈ code, Info.dynamic (stmtInfo s) = true := by
  rw [slice_block, (slice_fold_fields code _).2.2.2]
  simp

private theorem slice_stmtInfo_while (condition : Bap.Bil.Exp) (body : Bap.Bil.Program) :
    Info.defs (stmtInfo (.while condition body)) = [] ∧
    Info.mayDefs (stmtInfo (.while condition body)) =
      Info.defs (slice_block body) ++ Info.mayDefs (slice_block body) ∧
    Info.unknownWrite (stmtInfo (.while condition body)) = Info.unknownWrite (slice_block body) ∧
    Info.dynamic (stmtInfo (.while condition body)) = true := by
  obtain ⟨h1, h2, h3⟩ := slice_usesExp_pure condition
  simp [stmtInfo, merge, h1, h2, h3, slice_block]

private theorem slice_stmtInfo_ifElse (condition : Bap.Bil.Exp) (yes no : Bap.Bil.Program) :
    Info.defs (stmtInfo (.ifElse condition yes no)) =
      (Info.defs (slice_block yes)).filter (Info.defs (slice_block no)).contains ∧
    Info.mayDefs (stmtInfo (.ifElse condition yes no)) =
      Info.defs (slice_block yes) ++ Info.mayDefs (slice_block yes) ++ Info.defs (slice_block no) ++
        Info.mayDefs (slice_block no) ∧
    Info.unknownWrite (stmtInfo (.ifElse condition yes no)) =
      (Info.unknownWrite (slice_block yes) || Info.unknownWrite (slice_block no)) ∧
    (Info.dynamic (slice_block yes) = true → Info.dynamic (stmtInfo (.ifElse condition yes no)) = true) ∧
    (Info.dynamic (slice_block no) = true → Info.dynamic (stmtInfo (.ifElse condition yes no)) = true) := by
  obtain ⟨h1, h2, h3⟩ := slice_usesExp_pure condition
  simp +contextual [stmtInfo, merge, h1, h2, h3, slice_block]

/-- A location only counts as defined by a conditional if both branches define it. -/
theorem slice_ifElse_must_defs (condition : Bap.Bil.Exp) (yes no : Bap.Bil.Program) (d : Location) :
    d ∈ Info.defs (stmtInfo (.ifElse condition yes no)) ↔
      (∃ s ∈ yes, d ∈ Info.defs (stmtInfo s)) ∧ (∃ s ∈ no, d ∈ Info.defs (stmtInfo s)) := by
  rw [(slice_stmtInfo_ifElse condition yes no).1]
  simp [slice_block_defs]

/-- A one-armed conditional overwrites nothing for certain, so everything live after it stays live. -/
theorem slice_one_armed_if_keeps_live (condition : Bap.Bil.Exp) (yes : Bap.Bil.Program)
    (live : List Location) (loc : Location) (hl : loc ∈ live) :
    loc ∈ backwardInstruction live (stmtInfo (.ifElse condition yes [])) := by
  rw [slice_mem_backwardInstruction]
  refine .inl ⟨hl, fun d hd => ?_⟩
  have := ((slice_ifElse_must_defs condition yes [] d).mp hd).2
  simp at this

/-- A loop may run zero times, so everything live after it stays live. -/
theorem slice_while_keeps_live (condition : Bap.Bil.Exp) (body : Bap.Bil.Program)
    (live : List Location) (loc : Location) (hl : loc ∈ live) :
    loc ∈ backwardInstruction live (stmtInfo (.while condition body)) := by
  rw [slice_mem_backwardInstruction, (slice_stmtInfo_while condition body).1]
  simp [hl]

private theorem slice_unknownWrite_dynamic_stmt (stmt : Bap.Bil.Stmt) :
    Info.unknownWrite (stmtInfo stmt) = true → Info.dynamic (stmtInfo stmt) = true := by
  induction stmt using stmtInduction with
  | move var value =>
    cases hs : isStore value <;> cases ht : var.typ <;> simp +contextual [stmtInfo, hs, ht]
  | jmp target => simp [stmtInfo, (slice_usesExp_pure target).2.2]
  | special message => simp [stmtInfo]
  | cpuExn number => simp [stmtInfo]
  | while_ condition body _ => intro _; exact (slice_stmtInfo_while condition body).2.2.2
  | ifElse condition yes no ihy ihn =>
    intro h
    obtain ⟨_, _, h3, h4, h5⟩ := slice_stmtInfo_ifElse condition yes no
    rw [h3, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨s, hs, hu⟩ := (slice_block_unknownWrite yes).mp h
      exact h4 ((slice_block_dynamic yes).mpr ⟨s, hs, ihy s hs hu⟩)
    · obtain ⟨s, hs, hu⟩ := (slice_block_unknownWrite no).mp h
      exact h5 ((slice_block_dynamic no).mpr ⟨s, hs, ihn s hs hu⟩)

/-- A write to an undetermined address always clears `complete` at a site. -/
theorem slice_unknownWrite_dynamic (code : Bap.Bil.Program)
    (h : Info.unknownWrite (slice_block code) = true) : Info.dynamic (slice_block code) = true := by
  obtain ⟨s, hs, hu⟩ := (slice_block_unknownWrite code).mp h
  exact (slice_block_dynamic code).mpr ⟨s, hs, slice_unknownWrite_dynamic_stmt s hu⟩

private theorem slice_fold_accum (instructions : List Bap.Disasm.Insn) (live : List Location)
    (sites : List Nat) (complete : Bool) :
    instructions.foldl slice_step (live, sites, complete) =
      let result := instructions.foldl slice_step (live, [], true)
      (result.1, sites ++ result.2.1, complete && result.2.2) := by
  induction instructions generalizing live sites complete with
  | nil => simp
  | cons insn rest ih =>
    simp only [List.foldl_cons, slice_step]
    by_cases hrel : relevant live (slice_block insn.bil) = true
    · simp only [hrel, ite_true]
      rw [ih _ (sites ++ [insn.address]), ih _ ([] ++ [insn.address])]
      simp [Bool.and_assoc]
    · simp only [hrel, Bool.false_eq_true, ite_false]
      rw [ih live sites complete]

/-- Slicing a concatenation runs the suffix first and feeds its live set into the prefix. -/
theorem slice_backward_append (xs ys : List Bap.Disasm.Insn) (criteria : List Location) :
    let later := backward ys criteria
    let earlier := backward xs later.live
    (backward (xs ++ ys) criteria).sites = earlier.sites ++ later.sites ∧
      (backward (xs ++ ys) criteria).live = earlier.live ∧
      (backward (xs ++ ys) criteria).complete = (later.complete && earlier.complete) := by
  simp only [slice_backward_eq, List.reverse_append, List.foldl_append]
  rw [slice_fold_accum xs.reverse]
  simp

/-- A singleton slice takes the instruction exactly when it is relevant to the criteria. -/
theorem slice_backward_singleton (insn : Bap.Disasm.Insn) (criteria : List Location) :
    (backward [insn] criteria).sites =
      if relevant criteria (slice_block insn.bil) then [insn.address] else [] := by
  simp only [slice_backward_eq, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.foldl_cons, List.foldl_nil, slice_step]
  split <;> simp

private theorem slice_backward_singleton_complete (insn : Bap.Disasm.Insn) (criteria : List Location) :
    (backward [insn] criteria).complete =
      if relevant criteria (slice_block insn.bil) then !Info.dynamic (slice_block insn.bil) else true := by
  simp only [slice_backward_eq, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.foldl_cons, List.foldl_nil, slice_step]
  split <;> simp

/-- Sites are a subsequence of the input instruction addresses, in input order. -/
theorem slice_sites_sublist (instructions : List Bap.Disasm.Insn) (criteria : List Location) :
    (backward instructions criteria).sites.Sublist (instructions.map Bap.Disasm.Insn.address) := by
  have key : ∀ (rest : List Bap.Disasm.Insn) (live : List Location) (sites : List Nat) (complete : Bool),
      (rest.foldl slice_step (live, sites, complete)).2.1.Sublist
        (sites ++ rest.map Bap.Disasm.Insn.address) := by
    intro rest
    induction rest with
    | nil => simp
    | cons insn rest ih =>
      intro live sites complete
      simp only [List.foldl_cons, slice_step, List.map_cons]
      split
      · have := ih (backwardInstruction live (slice_block insn.bil)) (sites ++ [insn.address])
          (complete && !Info.dynamic (slice_block insn.bil))
        simpa using this
      · exact (ih live sites complete).trans
          (List.Sublist.append_left (List.sublist_cons_self _ _) _)
  have := (key instructions.reverse criteria [] true).reverse
  simpa [slice_backward_eq] using this

theorem slice_site_is_instruction {instructions : List Bap.Disasm.Insn} {criteria : List Location}
    {site : Nat} (h : site ∈ (backward instructions criteria).sites) :
    ∃ insn ∈ instructions, insn.address = site := by
  have := (slice_sites_sublist instructions criteria).subset h
  simpa using this

/-- Splits a slice around one instruction: `later` slices what follows it. -/
private theorem slice_backward_around (xs : List Bap.Disasm.Insn) (insn : Bap.Disasm.Insn)
    (ys : List Bap.Disasm.Insn) (criteria : List Location) :
    let later := backward ys criteria
    let here := backward [insn] later.live
    let earlier := backward xs here.live
    (backward (xs ++ insn :: ys) criteria).sites = earlier.sites ++ here.sites ++ later.sites ∧
      (backward (xs ++ insn :: ys) criteria).complete =
        (later.complete && (here.complete && earlier.complete)) := by
  have h1 := slice_backward_append xs (insn :: ys) criteria
  have h2 := slice_backward_append [insn] ys criteria
  simp only [List.singleton_append] at h2
  obtain ⟨h1s, _, h1c⟩ := h1
  obtain ⟨h2s, h2l, h2c⟩ := h2
  simp only [h1s, h1c, h2s, h2l, h2c, List.append_assoc]
  simp [Bool.and_assoc]

/-- An instruction relevant to what is live after it is a site. -/
theorem slice_relevant_is_site (xs : List Bap.Disasm.Insn) (insn : Bap.Disasm.Insn)
    (ys : List Bap.Disasm.Insn) (criteria : List Location)
    (h : relevant (backward ys criteria).live (slice_block insn.bil) = true) :
    insn.address ∈ (backward (xs ++ insn :: ys) criteria).sites := by
  rw [(slice_backward_around xs insn ys criteria).1, slice_backward_singleton]
  simp [h]

/-- An instruction whose effects can't be summarised statically is in every slice. -/
theorem slice_always_is_site (xs : List Bap.Disasm.Insn) (insn : Bap.Disasm.Insn)
    (ys : List Bap.Disasm.Insn) (criteria : List Location)
    (halways : Info.always (slice_block insn.bil) = true) :
    insn.address ∈ (backward (xs ++ insn :: ys) criteria).sites :=
  slice_relevant_is_site xs insn ys criteria ((slice_relevant_iff _ _).mpr (.inl halways))

/-- A store that overlaps a live location, even partly, makes its instruction a site. -/
theorem slice_overlapping_def_is_site (xs : List Bap.Disasm.Insn) (insn : Bap.Disasm.Insn)
    (ys : List Bap.Disasm.Insn) (criteria : List Location) {d loc : Location}
    (hd : d ∈ Info.defs (slice_block insn.bil) ∨ d ∈ Info.mayDefs (slice_block insn.bil))
    (hl : loc ∈ (backward ys criteria).live) (ho : d.overlaps loc = true) :
    insn.address ∈ (backward (xs ++ insn :: ys) criteria).sites := by
  apply slice_relevant_is_site
  rw [slice_relevant_iff]
  rcases hd with hd | hd
  · exact .inr (.inr (.inl ⟨d, hd, loc, hl, ho⟩))
  · exact .inr (.inr (.inr (.inl ⟨d, hd, loc, hl, ho⟩)))

/-- A store to an undetermined address may write any live memory: it is a site and the slice is
not complete. -/
theorem slice_unknown_write_incomplete (xs : List Bap.Disasm.Insn) (insn : Bap.Disasm.Insn)
    (ys : List Bap.Disasm.Insn) (criteria : List Location) {loc : Location}
    (hu : Info.unknownWrite (slice_block insn.bil) = true)
    (hl : loc ∈ (backward ys criteria).live) (hm : loc.isMemory = true) :
    insn.address ∈ (backward (xs ++ insn :: ys) criteria).sites ∧
      (backward (xs ++ insn :: ys) criteria).complete = false := by
  have hrel : relevant (backward ys criteria).live (slice_block insn.bil) = true :=
    (slice_relevant_iff _ _).mpr (.inr (.inl ⟨hu, loc, hl, hm⟩))
  refine ⟨slice_relevant_is_site xs insn ys criteria hrel, ?_⟩
  rw [(slice_backward_around xs insn ys criteria).2, slice_backward_singleton_complete]
  simp [hrel, slice_unknownWrite_dynamic _ hu]

/-- Soundness of `complete`, for the linear order `backward` assumes (`backwardProject` clears the
flag otherwise). Each instruction is either a site with a fully determined summary, or nothing it
may write overlaps what is live after it, and it writes no undetermined address while memory is
live. -/
theorem slice_complete_sound {xs ys : List Bap.Disasm.Insn} {insn : Bap.Disasm.Insn}
    {criteria : List Location} (h : (backward (xs ++ insn :: ys) criteria).complete = true) :
    let live := (backward ys criteria).live
    let info := slice_block insn.bil
    (insn.address ∈ (backward (xs ++ insn :: ys) criteria).sites ∧ Info.dynamic info = false ∧
        Info.unknownWrite info = false) ∨
      (relevant live info = false ∧ Info.always info = false ∧
        (∀ d, d ∈ Info.defs info ∨ d ∈ Info.mayDefs info → ∀ loc ∈ live, d.overlaps loc = false) ∧
        (Info.unknownWrite info = true → ∀ loc ∈ live, loc.isMemory = false)) := by
  intro live info
  rw [(slice_backward_around xs insn ys criteria).2, slice_backward_singleton_complete] at h
  by_cases hrel : relevant live info = true
  · refine .inl ⟨slice_relevant_is_site xs insn ys criteria hrel, ?_⟩
    have hd : Info.dynamic info = false := by
      simp only [Bool.and_eq_true] at h
      have := h.2.1
      simpa [live, info, hrel] using this
    refine ⟨hd, ?_⟩
    cases hu : Info.unknownWrite info with
    | false => rfl
    | true => rw [slice_unknownWrite_dynamic _ hu] at hd; cases hd
  · refine .inr ⟨by simpa using hrel, ?_, ?_, ?_⟩
    · cases ha : Info.always info with
      | false => rfl
      | true => exact absurd ((slice_relevant_iff _ _).mpr (.inl ha)) hrel
    · intro d hd loc hl
      cases ho : d.overlaps loc with
      | false => rfl
      | true =>
        refine absurd ((slice_relevant_iff _ _).mpr ?_) hrel
        rcases hd with hd | hd
        · exact .inr (.inr (.inl ⟨d, hd, loc, hl, ho⟩))
        · exact .inr (.inr (.inr (.inl ⟨d, hd, loc, hl, ho⟩)))
    · intro hu loc hl
      cases hm : loc.isMemory with
      | false => rfl
      | true => exact absurd ((slice_relevant_iff _ _).mpr (.inr (.inl ⟨hu, loc, hl, hm⟩))) hrel

/-- Everything a statement may write, as the slicer summarises it. -/
private def slice_writes (info : Info) : List Location := Info.defs info ++ Info.mayDefs info

private theorem slice_writes_move {var : Bap.Var} {value : Bap.Bil.Exp}
    (h : ¬ (var.typ matches .mem _ _)) : Location.reg var ∈ slice_writes (stmtInfo (.move var value)) := by
  revert h
  cases hs : isStore value <;> cases ht : var.typ <;> simp [slice_writes, stmtInfo, hs, ht]

private theorem slice_writes_while {condition : Bap.Bil.Exp} {body : Bap.Bil.Program}
    {s : Bap.Bil.Stmt} (hs : s ∈ body) {d : Location} (hd : d ∈ slice_writes (stmtInfo s)) :
    d ∈ slice_writes (stmtInfo (.while condition body)) := by
  simp only [slice_writes, List.mem_append, (slice_stmtInfo_while condition body).2.1,
    slice_block_defs, slice_block_mayDefs] at hd ⊢
  rcases hd with hd | hd
  · exact .inr (.inl ⟨s, hs, hd⟩)
  · exact .inr (.inr ⟨s, hs, hd⟩)

private theorem slice_writes_ifElse {condition : Bap.Bil.Exp} {yes no : Bap.Bil.Program}
    {s : Bap.Bil.Stmt} (hs : s ∈ yes ∨ s ∈ no) {d : Location} (hd : d ∈ slice_writes (stmtInfo s)) :
    d ∈ slice_writes (stmtInfo (.ifElse condition yes no)) := by
  simp only [slice_writes, List.mem_append, (slice_stmtInfo_ifElse condition yes no).2.1,
    slice_block_defs, slice_block_mayDefs] at hd ⊢
  rcases hs with hs | hs <;> rcases hd with hd | hd
  · exact .inr (.inl (.inl (.inl ⟨s, hs, hd⟩)))
  · exact .inr (.inl (.inl (.inr ⟨s, hs, hd⟩)))
  · exact .inr (.inl (.inr ⟨s, hs, hd⟩))
  · exact .inr (.inr ⟨s, hs, hd⟩)

private theorem slice_lookup_bind_other {env : Bap.Bil.Env} {var other : Bap.Var} (value : Bap.Value)
    (h : var ≠ other) : Bap.Bil.lookup (Bap.Bil.bind env var value) other = Bap.Bil.lookup env other := by
  have hfind : (List.filter (fun binding : Bap.Var × Bap.Value => binding.1 != var) env).find?
      (fun binding => binding.1 == other) = env.find? (fun binding => binding.1 == other) := by
    induction env with
    | nil => rfl
    | cons head tail ih =>
      by_cases hv : head.1 = var
      · simp [hv, h, ih]
      · simp only [List.filter_cons, bne_iff_ne, ne_eq, hv, not_false_eq_true, ite_true, List.find?_cons, ih]
  have hne : (var == other) = false := by simp [h]
  simp only [Bap.Bil.lookup, Bap.Bil.bind, List.find?_cons, hne, hfind]

private theorem slice_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => cases h

/-- Executing statements the slicer sees no write of `var` in leaves `var` alone. -/
private theorem slice_exec_frame (var : Bap.Var) (hvar : ¬ (var.typ matches .mem _ _)) (fuel : Nat) :
    (∀ (s : Bap.Bil.Stmt) (st st' : Bap.Bil.State) (e : Bap.Bil.Effect),
      Location.reg var ∉ slice_writes (stmtInfo s) → Bap.Bil.execStmt fuel st s = .ok (st', e) →
      Bap.Bil.lookup st'.env var = Bap.Bil.lookup st.env var) ∧
    (∀ (code : List Bap.Bil.Stmt) (st st' : Bap.Bil.State) (e : Bap.Bil.Effect),
      (∀ s ∈ code, Location.reg var ∉ slice_writes (stmtInfo s)) →
      Bap.Bil.execProgram fuel st code = .ok (st', e) →
      Bap.Bil.lookup st'.env var = Bap.Bil.lookup st.env var) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro s st st' e _ h
      simp [Bap.Bil.execStmt] at h
    · intro code st st' e _ h
      simp [Bap.Bil.execProgram] at h
  | succ fuel ih =>
    obtain ⟨ihs, ihp⟩ := ih
    refine ⟨?_, ?_⟩
    · intro s st st' e hw h
      cases s with
      | move target value =>
        simp only [Bap.Bil.execStmt, Bap.Bil.execExp] at h
        obtain ⟨val, _, h⟩ := slice_bind_ok h
        cases h
        apply slice_lookup_bind_other
        intro heq
        subst heq
        exact hw (slice_writes_move hvar)
      | jmp target =>
        simp only [Bap.Bil.execStmt, Bap.Bil.execExp] at h
        obtain ⟨_, _, h⟩ := slice_bind_ok h
        obtain ⟨_, _, h⟩ := slice_bind_ok h
        cases h
        rfl
      | special message =>
        simp only [Bap.Bil.execStmt] at h
        cases h
        rfl
      | cpuExn number =>
        simp only [Bap.Bil.execStmt] at h
        cases h
        rfl
      | ifElse condition yes no =>
        simp only [Bap.Bil.execStmt, Bap.Bil.execExp] at h
        obtain ⟨_, _, h⟩ := slice_bind_ok h
        obtain ⟨_, _, h⟩ := slice_bind_ok h
        split at h
        · split at h
          · exact ihp yes st st' e (fun s hs hd => hw (slice_writes_ifElse (.inl hs) hd)) h
          · exact ihp no st st' e (fun s hs hd => hw (slice_writes_ifElse (.inr hs) hd)) h
        · cases h
      | «while» condition body =>
        simp only [Bap.Bil.execStmt, Bap.Bil.execExp] at h
        obtain ⟨_, _, h⟩ := slice_bind_ok h
        obtain ⟨_, _, h⟩ := slice_bind_ok h
        split at h
        · split at h
          · obtain ⟨⟨next, effect⟩, hbody, h⟩ := slice_bind_ok h
            have h1 := ihp body st next effect (fun s hs hd => hw (slice_writes_while hs hd)) hbody
            cases effect with
            | normal => exact (ihs _ next st' e hw h).trans h1
            | jump _ => cases h; exact h1
            | special _ => cases h; exact h1
            | cpuExn _ => cases h; exact h1
          · cases h
            rfl
        · cases h
    · intro code st st' e hw h
      cases code with
      | nil =>
        simp only [Bap.Bil.execProgram] at h
        cases h
        rfl
      | cons head tail =>
        simp only [Bap.Bil.execProgram] at h
        obtain ⟨⟨next, effect⟩, hhead, h⟩ := slice_bind_ok h
        have h1 := ihs head st next effect (hw head List.mem_cons_self) hhead
        cases effect with
        | normal =>
          exact (ihp tail next st' e (fun s hs => hw s (List.mem_cons_of_mem _ hs)) h).trans h1
        | jump _ => cases h; exact h1
        | special _ => cases h; exact h1
        | cpuExn _ => cases h; exact h1

private theorem slice_block_writes {code : Bap.Bil.Program} {s : Bap.Bil.Stmt} (hs : s ∈ code)
    {d : Location} (hd : d ∈ slice_writes (stmtInfo s)) :
    d ∈ Info.defs (slice_block code) ∨ d ∈ Info.mayDefs (slice_block code) := by
  simp only [slice_writes, List.mem_append] at hd
  rcases hd with hd | hd
  · exact .inl ((slice_block_defs _ _).mpr ⟨s, hs, hd⟩)
  · exact .inr ((slice_block_mayDefs _ _).mpr ⟨s, hs, hd⟩)

/-- Semantic frame for registers: executing an instruction that is not relevant to `live`, however
the execution ends, leaves every live non-memory register's value unchanged. -/
theorem slice_irrelevant_preserves_registers {live : List Location} {insn : Bap.Disasm.Insn}
    (hrel : relevant live (slice_block insn.bil) = false) {var : Bap.Var}
    (hl : Location.reg var ∈ live) (hvar : ¬ (var.typ matches .mem _ _))
    {fuel : Nat} {st st' : Bap.Bil.State} {e : Bap.Bil.Effect}
    (h : Bap.Bil.execProgram fuel st insn.bil = .ok (st', e)) :
    Bap.Bil.lookup st'.env var = Bap.Bil.lookup st.env var := by
  refine (slice_exec_frame var hvar fuel).2 insn.bil st st' e (fun s hs hd => ?_) h
  have hself : (Location.reg var).overlaps (.reg var) = true := by simp [Location.overlaps]
  have : relevant live (slice_block insn.bil) = true := by
    rw [slice_relevant_iff]
    rcases slice_block_writes hs hd with hb | hb
    · exact .inr (.inr (.inl ⟨_, hb, _, hl, hself⟩))
    · exact .inr (.inr (.inr (.inl ⟨_, hb, _, hl, hself⟩)))
  rw [this] at hrel
  cases hrel

/-- `inner` occurs in `outer`, at any depth. -/
inductive slice_SubStmt : Bap.Bil.Stmt → Bap.Bil.Stmt → Prop where
  | refl (s : Bap.Bil.Stmt) : slice_SubStmt s s
  | loop {inner s : Bap.Bil.Stmt} {condition : Bap.Bil.Exp} {body : Bap.Bil.Program}
      (hs : s ∈ body) (h : slice_SubStmt inner s) : slice_SubStmt inner (.while condition body)
  | branch {inner s : Bap.Bil.Stmt} {condition : Bap.Bil.Exp} {yes no : Bap.Bil.Program}
      (hs : s ∈ yes ∨ s ∈ no) (h : slice_SubStmt inner s) : slice_SubStmt inner (.ifElse condition yes no)

private theorem slice_subStmt_writes {inner outer : Bap.Bil.Stmt} (h : slice_SubStmt inner outer) :
    (∀ d ∈ slice_writes (stmtInfo inner), d ∈ slice_writes (stmtInfo outer)) ∧
      (Info.unknownWrite (stmtInfo inner) = true → Info.unknownWrite (stmtInfo outer) = true) := by
  induction h with
  | refl => exact ⟨fun _ h => h, id⟩
  | loop hs _ ih =>
    refine ⟨fun d hd => slice_writes_while hs (ih.1 d hd), fun hu => ?_⟩
    rw [(slice_stmtInfo_while _ _).2.2.1]
    exact (slice_block_unknownWrite _).mpr ⟨_, hs, ih.2 hu⟩
  | branch hs _ ih =>
    refine ⟨fun d hd => slice_writes_ifElse hs (ih.1 d hd), fun hu => ?_⟩
    rw [(slice_stmtInfo_ifElse _ _ _).2.2.1, Bool.or_eq_true]
    rcases hs with hs | hs
    · exact .inl ((slice_block_unknownWrite _).mpr ⟨_, hs, ih.2 hu⟩)
    · exact .inr ((slice_block_unknownWrite _).mpr ⟨_, hs, ih.2 hu⟩)

/-- `store` is a node on the chain of stores a memory expression is built from. -/
inductive slice_StoreOf : Bap.Bil.Exp → Bap.Bil.Exp → Prop where
  | self (e : Bap.Bil.Exp) : slice_StoreOf e e
  | inner {store memory address value : Bap.Bil.Exp} {endian : Bap.Endian} {size : Nat}
      (h : slice_StoreOf store memory) :
      slice_StoreOf store (.store memory address value endian size)

/-- Every store of a chain is accounted for: at its constant address, or as an undetermined write. -/
theorem slice_memoryWrites_complete {dst : Bap.Var} {value memory address stored : Bap.Bil.Exp}
    {endian : Bap.Endian} {size : Nat}
    (h : slice_StoreOf (.store memory address stored endian size) value) :
    (∃ n, constant address = some n ∧ Location.mem n size ∈ (memoryWrites dst value).1) ∨
      (constant address = none ∧ (memoryWrites dst value).2 = true) := by
  generalize hnode : Bap.Bil.Exp.store memory address stored endian size = node at h
  induction h with
  | self =>
    subst hnode
    cases hc : constant address with
    | none => exact .inr ⟨rfl, by simp [memoryWrites, hc]⟩
    | some n => exact .inl ⟨n, rfl, by simp [memoryWrites, hc]⟩
  | @inner m a _ _ s _ ih =>
    rcases ih with ⟨n, hn, hm⟩ | ⟨hn, hu⟩
    · refine .inl ⟨n, hn, ?_⟩
      simp only [memoryWrites]
      cases hc : constant a <;> simp [hm]
    · refine .inr ⟨hn, ?_⟩
      simp only [memoryWrites]
      cases hc : constant a <;> simp [hu]

private theorem slice_stmtInfo_move_store (var : Bap.Var) (value : Bap.Bil.Exp)
    (hmem : (isStore value || var.typ matches .mem _ _) = true) :
    (∀ d ∈ (memoryWrites var value).1, d ∈ slice_writes (stmtInfo (.move var value))) ∧
      Info.unknownWrite (stmtInfo (.move var value)) = (memoryWrites var value).2 := by
  revert hmem
  cases hs : isStore value <;> cases ht : var.typ <;>
    simp +contextual [slice_writes, stmtInfo, hs, ht]

/-- Memory frame, syntactically: every memory assignment at any depth of an instruction that is
not relevant to `live` writes constant ranges disjoint from `live`, and writes an undetermined
address only if no memory is live. A statement about addresses: `Memory.write` itself rests on a
`partial` loop, so the byte contents after the write can't be derived here. -/
theorem slice_irrelevant_store_frame {live : List Location} {insn : Bap.Disasm.Insn}
    (hrel : relevant live (slice_block insn.bil) = false) {outer : Bap.Bil.Stmt}
    (houter : outer ∈ insn.bil) {var : Bap.Var} {value : Bap.Bil.Exp}
    (hsub : slice_SubStmt (.move var value) outer)
    (hmem : (isStore value || var.typ matches .mem _ _) = true) :
    (∀ d ∈ (memoryWrites var value).1, ∀ loc ∈ live, d.overlaps loc = false) ∧
      ((memoryWrites var value).2 = true → ∀ loc ∈ live, loc.isMemory = false) := by
  obtain ⟨hw, hu⟩ := slice_subStmt_writes hsub
  obtain ⟨hwm, hum⟩ := slice_stmtInfo_move_store var value hmem
  have hnot : relevant live (slice_block insn.bil) ≠ true := by simp [hrel]
  constructor
  · intro d hd loc hl
    cases ho : d.overlaps loc with
    | false => rfl
    | true =>
      refine absurd ((slice_relevant_iff _ _).mpr ?_) hnot
      rcases slice_block_writes houter (hw d (hwm d hd)) with hb | hb
      · exact .inr (.inr (.inl ⟨d, hb, loc, hl, ho⟩))
      · exact .inr (.inr (.inr (.inl ⟨d, hb, loc, hl, ho⟩)))
  · intro hflag loc hl
    cases hm : loc.isMemory with
    | false => rfl
    | true =>
      refine absurd ((slice_relevant_iff _ _).mpr (.inr (.inl ⟨?_, loc, hl, hm⟩))) hnot
      exact (slice_block_unknownWrite _).mpr ⟨outer, houter, hu (hum.trans hflag)⟩

section Regression

private def slice_x : Bap.Var := ⟨"x", .imm 64, 0, false⟩
private def slice_y : Bap.Var := ⟨"y", .imm 64, 0, false⟩
private def slice_c : Bap.Var := ⟨"c", .imm 1, 0, false⟩
private def slice_mem : Bap.Var := ⟨"m", .mem 64 8, 0, false⟩

private def slice_condInsns : List Bap.Disasm.Insn := [
  ⟨0, 1, "x = 5", .normal, none, [.move slice_x (.int (BitVec.ofNat 64 5))]⟩,
  ⟨1, 1, "if c then x = 1", .normal, none,
    [.ifElse (.var slice_c) [.move slice_x (.int (BitVec.ofNat 64 1))] []]⟩]

private def slice_storeAt (address size : Nat) : Bap.Disasm.Insn :=
  ⟨0, 1, "store", .normal, none,
    [.move slice_mem (.store (.var slice_mem) (.int (BitVec.ofNat 64 address))
      (.int (BitVec.ofNat (size * 8) 7)) .little size)]⟩

private def slice_dynamicStore : Bap.Disasm.Insn :=
  ⟨0, 1, "store", .normal, none,
    [.move slice_mem (.store (.var slice_mem) (.var slice_y) (.int (BitVec.ofNat 8 7)) .little 1)]⟩

set_option linter.unusedSimpArgs false

/-- `x` keeps its first value if the branch isn't taken, so both definitions are in the slice. -/
theorem slice_conditional_def_regression :
    (backward slice_condInsns [.reg slice_x]).sites = [0, 1] := by
  simp [slice_backward_eq, slice_step, slice_block, stmtInfo, merge, usesExp, relevant, touches,
    backwardInstruction, removeDefinitions, addUnique, Location.overlaps, Location.covers,
    Location.isMemory, memoryWrites, constant, isStore, Bap.Bil.evalExp, Bap.Value.asBits, Bap.Bil.lookup, Except.toOption,
    slice_condInsns, slice_storeAt, slice_dynamicStore, slice_x, slice_y, slice_c, slice_mem]

/-- An 8-byte store over a 4-byte criterion is a site and fully overwrites it. -/
theorem slice_covering_store_regression :
    (backward [slice_storeAt 100 8] [.mem 100 4]).sites = [0] ∧
      (backward [slice_storeAt 100 8] [.mem 100 4]).live = [] ∧
      (backward [slice_storeAt 100 8] [.mem 100 4]).complete = true := by
  simp [slice_backward_eq, slice_step, slice_block, stmtInfo, merge, usesExp, relevant, touches,
    backwardInstruction, removeDefinitions, addUnique, Location.overlaps, Location.covers,
    Location.isMemory, memoryWrites, constant, isStore, Bap.Bil.evalExp, Bap.Value.asBits, Bap.Bil.lookup, Except.toOption,
    slice_condInsns, slice_storeAt, slice_dynamicStore, slice_x, slice_y, slice_c, slice_mem]

/-- A 4-byte store over half of an 8-byte criterion is a site that leaves the criterion live. -/
theorem slice_partial_store_regression :
    (backward [slice_storeAt 104 4] [.mem 100 8]).sites = [0] ∧
      (backward [slice_storeAt 104 4] [.mem 100 8]).live = [.mem 100 8] := by
  simp [slice_backward_eq, slice_step, slice_block, stmtInfo, merge, usesExp, relevant, touches,
    backwardInstruction, removeDefinitions, addUnique, Location.overlaps, Location.covers,
    Location.isMemory, memoryWrites, constant, isStore, Bap.Bil.evalExp, Bap.Value.asBits, Bap.Bil.lookup, Except.toOption,
    slice_condInsns, slice_storeAt, slice_dynamicStore, slice_x, slice_y, slice_c, slice_mem]

/-- A store to an unknown address may write the criterion: a site, and the slice is incomplete. -/
theorem slice_dynamic_store_regression :
    (backward [slice_dynamicStore] [.mem 100 1]).sites = [0] ∧
      (backward [slice_dynamicStore] [.mem 100 1]).complete = false := by
  simp [slice_backward_eq, slice_step, slice_block, stmtInfo, merge, usesExp, relevant, touches,
    backwardInstruction, removeDefinitions, addUnique, Location.overlaps, Location.covers,
    Location.isMemory, memoryWrites, constant, isStore, Bap.Bil.evalExp, Bap.Value.asBits, Bap.Bil.lookup, Except.toOption,
    slice_condInsns, slice_storeAt, slice_dynamicStore, slice_x, slice_y, slice_c, slice_mem]

end Regression

/-- The instructions `backwardProject` slices. -/
private def slice_functionInsns (project : Bap.Project.Project) (entry : Nat) : List Bap.Disasm.Insn :=
  let index := Bap.Analysis.Xrefs.create project
  let owner := (Bap.Analysis.Xrefs.functionOf index entry).map Bap.Image.Symbol.addr
  project.disasm.map (fun disasm =>
    if owner.isSome then
      disasm.instructions.filter fun insn =>
        (Bap.Analysis.Xrefs.functionOf index insn.address).map Bap.Image.Symbol.addr = owner
    else
      disasm.instructions) |>.getD []

/-- `backwardProject` claims `complete` only if the function's listing order is an execution order:
no conditional or indirect jump, and no direct jump back into the listing. Calls remain: the slice
is intraprocedural and callee effects are out of its scope. -/
theorem slice_backwardProject_complete_linear {project : Bap.Project.Project} {entry : Nat}
    {criteria : List Location} (h : (backwardProject project entry criteria).complete = true) :
    let insns := slice_functionInsns project entry
    (backward insns criteria).complete = true ∧ ∀ insn ∈ insns,
      insn.flow ≠ .conditionalJump ∧ insn.flow ≠ .indirectJump ∧
        (insn.flow = .jump → ∀ target, insn.target = some target → target ∉ insns.map Bap.Disasm.Insn.address) := by
  intro insns
  have heq : (backwardProject project entry criteria).complete =
      ((backward insns criteria).complete && linear insns) := rfl
  rw [heq, Bool.and_eq_true] at h
  refine ⟨h.1, fun insn hi => ?_⟩
  have hl := List.all_eq_true.mp h.2 insn hi
  revert hl
  cases hf : insn.flow <;> simp
  intro hl target ht
  simpa [ht] using hl

private theorem slice_relevant_mono {small big : List Location} {info : Info}
    (h : ∀ loc ∈ small, loc ∈ big) (hrel : relevant small info = true) : relevant big info = true := by
  rw [slice_relevant_iff] at hrel ⊢
  rcases hrel with h' | ⟨hu, l, hl, hm⟩ | ⟨d, hd, l, hl, ho⟩ | ⟨d, hd, l, hl, ho⟩ | ⟨d, hd, l, hl, ho⟩
  · exact .inl h'
  · exact .inr (.inl ⟨hu, l, h _ hl, hm⟩)
  · exact .inr (.inr (.inl ⟨d, hd, l, h _ hl, ho⟩))
  · exact .inr (.inr (.inr (.inl ⟨d, hd, l, h _ hl, ho⟩)))
  · exact .inr (.inr (.inr (.inr ⟨d, hd, l, h _ hl, ho⟩)))

private theorem slice_fold_mono (instructions : List Bap.Disasm.Insn) :
    ∀ (small big : List Location × List Nat × Bool),
      (∀ loc ∈ small.1, loc ∈ big.1) → small.2.1.Sublist big.2.1 → (big.2.2 = true → small.2.2 = true) →
      let small' := instructions.foldl slice_step small
      let big' := instructions.foldl slice_step big
      (∀ loc ∈ small'.1, loc ∈ big'.1) ∧ small'.2.1.Sublist big'.2.1 ∧ (big'.2.2 = true → small'.2.2 = true) := by
  induction instructions with
  | nil => intro _ _ h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons insn rest ih =>
    rintro ⟨liveS, sitesS, completeS⟩ ⟨liveB, sitesB, completeB⟩ h1 h2 h3
    simp only [List.foldl_cons]
    simp only at h1 h2 h3
    apply ih
    all_goals
      by_cases hS : relevant liveS (slice_block insn.bil) = true
      · have hB := slice_relevant_mono h1 hS
        simp only [slice_step, hS, hB, ite_true]
        first
          | (intro loc hloc
             simp only [slice_mem_backwardInstruction] at hloc ⊢
             exact hloc.imp (fun h => ⟨h1 _ h.1, h.2⟩) id)
          | exact List.Sublist.append h2 (List.Sublist.refl _)
          | (intro h
             simp only [Bool.and_eq_true] at h ⊢
             exact ⟨h3 h.1, h.2⟩)
      · by_cases hB : relevant liveB (slice_block insn.bil) = true
        · simp only [slice_step, hS, hB, Bool.false_eq_true, ite_true, ite_false]
          first
            | (intro loc hloc
               rw [slice_mem_backwardInstruction]
               refine .inl ⟨h1 _ hloc, fun d hd => ?_⟩
               cases hc : d.covers loc with
               | false => rfl
               | true =>
                 exact absurd ((slice_relevant_iff _ _).mpr
                   (.inr (.inr (.inl ⟨d, hd, loc, hloc, slice_covers_overlaps hc⟩)))) hS)
            | exact h2.trans (List.sublist_append_left _ _)
            | (intro h
               simp only [Bool.and_eq_true] at h
               exact h3 h.1)
        · simp only [slice_step, hS, hB, Bool.false_eq_true, ite_false]
          first
            | exact h1
            | exact h2
            | exact h3

/-- Enlarging the criteria can only enlarge the slice: more live locations, a super-sequence of
sites, and a completeness claim that implies the smaller slice's claim. -/
theorem slice_backward_mono (instructions : List Bap.Disasm.Insn) {small big : List Location}
    (h : ∀ loc ∈ small, loc ∈ big) :
    (∀ loc ∈ (backward instructions small).live, loc ∈ (backward instructions big).live) ∧
    (backward instructions small).sites.Sublist (backward instructions big).sites ∧
    ((backward instructions big).complete = true → (backward instructions small).complete = true) := by
  obtain ⟨h1, h2, h3⟩ := slice_fold_mono instructions.reverse (small, [], true) (big, [], true) h (by simp) (by simp)
  exact ⟨h1, List.Sublist.reverse h2, h3⟩

end Slice

section DynamicSlice
open Bap.Analysis.DynamicSlice
open_private Bap.Analysis.DynamicSlice in Bap.Analysis.DynamicSlice : writesCriterion

theorem dynslice_writesCriterion_iff (access : Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location) :
    writesCriterion access criteria = true ↔
      access.write = true ∧ ∃ criterion ∈ criteria,
        (Bap.Analysis.Slice.Location.mem access.address access.size).overlaps criterion = true := by
  simp [writesCriterion]

/-- Dynamic sites are the static slice's sites restricted to the executed program counters,
in static order. -/
theorem dynslice_mem_sites_iff (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location) (site : Nat) :
    site ∈ (backwardWithAccesses project entry pcs accesses criteria).sites ↔
      site ∈ (Bap.Analysis.Slice.backwardProject project entry criteria).sites ∧ site ∈ pcs := by
  simp [backwardWithAccesses]

theorem dynslice_sites_sublist_static (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location) :
    (backwardWithAccesses project entry pcs accesses criteria).sites.Sublist
      (Bap.Analysis.Slice.backwardProject project entry criteria).sites :=
  List.filter_sublist

/-- A gap is either a static site the trace never executed, or a traced write to a criterion
from a program counter outside the static slice. -/
theorem dynslice_mem_gaps_iff (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location) (gap : Nat) :
    gap ∈ (backwardWithAccesses project entry pcs accesses criteria).gaps ↔
      (gap ∈ (Bap.Analysis.Slice.backwardProject project entry criteria).sites ∧ gap ∉ pcs) ∨
      ∃ access ∈ accesses, access.pc = gap ∧ writesCriterion access criteria = true ∧
        gap ∉ (Bap.Analysis.Slice.backwardProject project entry criteria).sites := by
  simp only [backwardWithAccesses, List.mem_eraseDups, List.mem_append, List.mem_filter, List.mem_filterMap]
  apply or_congr
  · simp
  · constructor
    · rintro ⟨access, ha, h⟩
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hc
        exact ⟨access, ha, rfl, hc.1, hc.2⟩
      · simp at h
    · rintro ⟨access, ha, rfl, hw, hs⟩
      exact ⟨access, ha, by simp [hw, hs]⟩

theorem dynslice_gaps_nodup (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location) :
    (backwardWithAccesses project entry pcs accesses criteria).gaps.Nodup :=
  callgraph_eraseDups_nodup _

theorem dynslice_complete_iff (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location) :
    (backwardWithAccesses project entry pcs accesses criteria).complete = true ↔
      (Bap.Analysis.Slice.backwardProject project entry criteria).complete = true ∧
        (backwardWithAccesses project entry pcs accesses criteria).gaps = [] := by
  simp [backwardWithAccesses]

/-- Without access records the only possible gaps are unexecuted static sites. -/
theorem dynslice_backward_gaps_iff (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (criteria : List Bap.Analysis.Slice.Location) (gap : Nat) :
    gap ∈ (backward project entry pcs criteria).gaps ↔
      gap ∈ (Bap.Analysis.Slice.backwardProject project entry criteria).sites ∧ gap ∉ pcs := by
  rw [backward, dynslice_mem_gaps_iff]
  simp

/-- A trace that covers every static site, with no write from outside the slice, reproduces the
static slice exactly. -/
theorem dynslice_full_coverage (project : Bap.Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Bap.Emu.TraceAccess) (criteria : List Bap.Analysis.Slice.Location)
    (hcover : ∀ site ∈ (Bap.Analysis.Slice.backwardProject project entry criteria).sites, site ∈ pcs)
    (hinside : ∀ access ∈ accesses, writesCriterion access criteria = true →
      access.pc ∈ (Bap.Analysis.Slice.backwardProject project entry criteria).sites) :
    let result := backwardWithAccesses project entry pcs accesses criteria
    let static := Bap.Analysis.Slice.backwardProject project entry criteria
    result.sites = static.sites ∧ result.gaps = [] ∧ result.live = static.live ∧
      result.complete = static.complete := by
  have hgaps : (backwardWithAccesses project entry pcs accesses criteria).gaps = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro gap hg
    rcases (dynslice_mem_gaps_iff _ _ _ _ _ gap).mp hg with ⟨hs, hp⟩ | ⟨access, ha, rfl, hw, hs⟩
    · exact hp (hcover gap hs)
    · exact hs (hinside access ha hw)
  refine ⟨?_, hgaps, rfl, ?_⟩
  · simp only [backwardWithAccesses]
    apply List.filter_eq_self.mpr
    intro site hs
    simpa using hcover site hs
  · have hg := hgaps
    simp only [backwardWithAccesses] at hg ⊢
    rw [hg]
    simp

end DynamicSlice

section Propagate

set_option linter.unusedSimpArgs false

open Bap.Bil
open Bap.Analysis.Propagate
open_private Bap.Analysis.Propagate in Bap.Analysis.Propagate : sameConstant

/-- `b` reproduces every successful lookup of `a`. -/
def propagate_Extends (a b : Env) : Prop :=
  ∀ v r, lookup a v = .ok r → lookup b v = .ok r

private theorem propagate_find_filter (env : Env) (k w : Bap.Var) (h : w ≠ k) :
    (env.filter fun b => b.1 != k).find? (fun b => b.1 == w) = env.find? (fun b => b.1 == w) := by
  induction env with
  | nil => rfl
  | cons head tail ih =>
    by_cases hv : head.1 = k
    · have : head.1 ≠ w := fun e => h (e.symm.trans hv)
      simp [hv, List.filter_cons, List.find?_cons, h.symm, this] at ih ⊢
      exact ih
    · by_cases hw : head.1 = w
      · simp [hv, hw, List.filter_cons, List.find?_cons, h]
      · simp [hv, hw, List.filter_cons, List.find?_cons, ih] at ih ⊢

theorem propagate_lookup_bind (env : Env) (v w : Bap.Var) (r : Value) :
    lookup (Bil.bind env v r) w = if w = v then .ok r else lookup env w := by
  by_cases h : w = v
  · subst h; simp [lookup, Bil.bind]
  · have hh : ¬ v = w := fun e => h e.symm
    unfold lookup Bil.bind
    rw [List.find?_cons]
    have e : ((v, r).1 == w) = false := by simpa using hh
    rw [e]
    simp only [h, ite_false]
    rw [propagate_find_filter env v w h]

private theorem propagate_Extends_bind {a b : Env} (h : propagate_Extends a b) (v : Bap.Var) (r : Value) :
    propagate_Extends (Bil.bind a v r) (Bil.bind b v r) := by
  intro w s hs
  rw [propagate_lookup_bind] at hs ⊢
  split at hs
  · simp [*] at hs ⊢
  · simp only [*, ite_false]; exact h w s hs

private def propagate_R {α} (x y : Except String α) : Prop := ∀ v, x = .ok v → y = .ok v

private theorem propagate_R_refl {α} (x : Except String α) : propagate_R x x := fun _ h => h

private theorem propagate_R_bind {α β} {x y : Except String α} {f g : α → Except String β}
    (h : propagate_R x y) (k : ∀ v, propagate_R (f v) (g v)) : propagate_R (x >>= f) (y >>= g) := by
  intro r hr
  cases hx : x with
  | error e => rw [hx] at hr; cases hr
  | ok v =>
    rw [hx] at hr
    rw [h v hx]
    exact k v r hr

private theorem propagate_bind_ok {α β ε} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => cases h

/-- Evaluation is stable under extending the environment. -/
theorem propagate_eval_extends (e : Exp) : ∀ {a b : Env}, propagate_Extends a b →
    ∀ r, evalExp a e = .ok r → evalExp b e = .ok r := by
  have main : ∀ {a b : Env}, propagate_Extends a b → propagate_R (evalExp a e) (evalExp b e) := by
    induction e with
    | int v => intro a b _; exact propagate_R_refl _
    | var v => intro a b h; simp only [evalExp]; exact h v
    | load m ad _ _ im ia =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (im h) fun _ => propagate_R_bind (propagate_R_refl _) fun _ =>
        propagate_R_bind (ia h) fun _ => propagate_R_refl _
    | store m ad val _ _ im ia iv =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (im h) fun _ => propagate_R_bind (propagate_R_refl _) fun _ =>
        propagate_R_bind (ia h) fun _ => propagate_R_bind (propagate_R_refl _) fun _ =>
        propagate_R_bind (iv h) fun _ => propagate_R_refl _
    | bin _ _ _ il ir =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (il h) fun _ => propagate_R_bind (propagate_R_refl _) fun _ =>
        propagate_R_bind (ir h) fun _ => propagate_R_refl _
    | un _ _ i =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (i h) fun _ => propagate_R_refl _
    | cast _ _ _ i =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (i h) fun _ => propagate_R_refl _
    | letIn v _ _ il ib =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (il h) fun r => ib (propagate_Extends_bind h v r)
    | ite _ _ _ ic iy in_ =>
      intro a b h
      simp only [evalExp]
      refine propagate_R_bind (ic h) fun _ => propagate_R_bind (propagate_R_refl _) ?_
      rintro ⟨w, cv⟩
      by_cases hw : w = 1
      · subst hw
        simp only [dite_true]
        split
        · exact iy h
        · exact in_ h
      · simpa [hw] using propagate_R_refl _
    | extract _ _ _ i =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (i h) fun _ => propagate_R_refl _
    | concat _ _ il ir =>
      intro a b h
      simp only [evalExp]
      exact propagate_R_bind (il h) fun _ => propagate_R_bind (propagate_R_refl _) fun _ =>
        propagate_R_bind (ir h) fun _ => propagate_R_refl _
    | unknown _ _ => intro a b _; exact propagate_R_refl _
  intro a b h r k
  exact main h r k

private theorem propagate_Extends_nil (env : Env) : propagate_Extends [] env := by
  intro v r h; simp [lookup] at h

/-- A closed expression (one that evaluates in the empty environment) evaluates to the same
value everywhere. -/
theorem propagate_eval_closed {e : Exp} {r : Value} (env : Env) (h : evalExp [] e = .ok r) :
    evalExp env e = .ok r :=
  propagate_eval_extends e (propagate_Extends_nil env) r h

/-- Constant folding preserves evaluation exactly, in every environment, including failures. -/
theorem propagate_foldExp_eval (e : Exp) : ∀ env, evalExp env (foldExp e) = evalExp env e := by
  have folded : ∀ {e : Exp} {w} {v : BitVec w} (env : Env), evalExp [] e = .ok (.bits v) →
      evalExp env (Exp.int v) = evalExp env e := by
    intro e w v env h
    rw [propagate_eval_closed env h]; rfl
  induction e with
  | int v => intro env; rw [foldExp]; split <;> first | exact folded env ‹_› | rfl
  | var v => intro env; rw [foldExp]; split <;> first | exact folded env ‹_› | rfl
  | unknown _ _ => intro env; rw [foldExp]; split <;> first | exact folded env ‹_› | rfl
  | load _ _ _ _ im ia =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, im, ia]
  | store _ _ _ _ _ im ia iv =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, im, ia, iv]
  | bin _ _ _ il ir =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, il, ir]
  | un _ _ i =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, i]
  | cast _ _ _ i =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, i]
  | letIn _ _ _ il ib =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, il, ib]
  | ite _ _ _ ic iy in_ =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, ic, iy, in_]
  | extract _ _ _ i =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, i]
  | concat _ _ il ir =>
    intro env; rw [foldExp]; split
    · exact folded env ‹_›
    · simp only [evalExp, il, ir]

/-- Every known entry is a literal that matches the environment. -/
def propagate_KnownSound (known : Known) (env : Env) : Prop :=
  ∀ v r, (v, r) ∈ known →
    ∃ (w : Nat) (c : BitVec w), r = .int c ∧ lookup env v = .ok (.bits c)

theorem propagate_KnownSound_empty (env : Env) : propagate_KnownSound [] env := by
  intro v r h; simp at h

private theorem propagate_get_mem {known : Known} {v : Bap.Var} {r : Exp}
    (h : Assoc.get v known = some r) : (v, r) ∈ known := by
  unfold Assoc.get at h
  induction known with
  | nil => simp at h
  | cons head tail ih =>
    rcases head with ⟨a, b⟩
    rw [List.lookup_cons] at h
    by_cases hv : v = a
    · subst hv
      simp at h
      simp [h]
    · have hb : (v == a) = false := by simp [hv]
      rw [hb] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem propagate_KnownSound_filter_bind {known : Known} {env : Env}
    (h : propagate_KnownSound known env) (v : Bap.Var) (r : Value) :
    propagate_KnownSound (known.filter fun b => b.1 != v) (Bil.bind env v r) := by
  intro w s hs
  simp only [List.mem_filter, bne_iff_ne] at hs
  rcases h w s hs.1 with ⟨n, c, hc, hl⟩
  exact ⟨n, c, hc, by rw [propagate_lookup_bind]; simp [hs.2, hl]⟩

/-- Substituting sound constants preserves evaluation exactly. -/
theorem propagate_substitute_eval (e : Exp) : ∀ (known : Known) (env : Env),
    propagate_KnownSound known env → evalExp env (substitute known e) = evalExp env e := by
  induction e with
  | int _ => intros; rfl
  | var v =>
    intro known env h
    simp only [substitute, evalExp]
    cases hg : Assoc.get v known with
    | none => rfl
    | some r =>
      rcases h v r (propagate_get_mem hg) with ⟨w, c, rfl, hl⟩
      simp [evalExp, hl]
  | load _ _ _ _ im ia => intro known env h; simp only [substitute, evalExp, im _ _ h, ia _ _ h]
  | store _ _ _ _ _ im ia iv =>
    intro known env h; simp only [substitute, evalExp, im _ _ h, ia _ _ h, iv _ _ h]
  | bin _ _ _ il ir => intro known env h; simp only [substitute, evalExp, il _ _ h, ir _ _ h]
  | un _ _ i => intro known env h; simp only [substitute, evalExp, i _ _ h]
  | cast _ _ _ i => intro known env h; simp only [substitute, evalExp, i _ _ h]
  | letIn v _ _ il ib =>
    intro known env h
    simp only [substitute]
    split
    · rename_i hany
      obtain ⟨⟨w, s⟩, hs, hc⟩ := List.any_eq_true.1 hany
      rcases h w s (List.mem_filter.1 hs).1 with ⟨n, c, rfl, _⟩
      simp [occursFree] at hc
    · simp only [evalExp, il _ _ h]
      congr 1
      funext r
      exact ib _ _ (propagate_KnownSound_filter_bind h v r)
  | ite _ _ _ ic iy in_ =>
    intro known env h; simp only [substitute, evalExp, ic _ _ h, iy _ _ h, in_ _ _ h]
  | extract _ _ _ i => intro known env h; simp only [substitute, evalExp, i _ _ h]
  | concat _ _ il ir => intro known env h; simp only [substitute, evalExp, il _ _ h, ir _ _ h]
  | unknown _ _ => intros; rfl

/-- `simplify` is semantics preserving whenever the known constants hold. -/
theorem propagate_simplify_eval (known : Known) (env : Env) (e : Exp)
    (h : propagate_KnownSound known env) : evalExp env (simplify known e) = evalExp env e := by
  rw [simplify, propagate_foldExp_eval, propagate_substitute_eval e known env h]

private theorem propagate_sameConstant_int {a : Exp} {w : Nat} {c : BitVec w}
    (h : sameConstant a (.int c) = true) : a = .int c := by
  cases a <;> simp only [sameConstant, Bool.false_eq_true] at h
  rename_i w' c'
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hv⟩ := h
  rw [BitVec.eq_of_toNat_eq hv]

theorem propagate_mem_meet {left right : Known} {entry : Bap.Var × Exp} :
    entry ∈ meet left right ↔
      entry ∈ left ∧ (Assoc.get entry.1 right).any (sameConstant entry.2) = true := by
  simp [meet, List.mem_filter]

/-- Facts agreed with `right` hold wherever `right` is sound. -/
private theorem propagate_sound_of_agree {keep right : Known} {env : Env}
    (ha : ∀ entry ∈ keep, (Assoc.get entry.1 right).any (sameConstant entry.2) = true)
    (h : propagate_KnownSound right env) : propagate_KnownSound keep env := by
  intro v r hm
  have := ha (v, r) hm
  cases hg : Assoc.get v right with
  | none => simp [hg] at this
  | some s =>
    rcases h v s (propagate_get_mem hg) with ⟨w, c, rfl, hl⟩
    simp only [hg, Option.any_some] at this
    exact ⟨w, c, propagate_sameConstant_int this, hl⟩

/-- What both paths know holds if the first was taken. -/
theorem propagate_meet_sound_left {left right : Known} {env : Env}
    (h : propagate_KnownSound left env) : propagate_KnownSound (meet left right) env :=
  fun v r hm => h v r (propagate_mem_meet.mp hm).1

/-- What both paths know holds if the second was taken. -/
theorem propagate_meet_sound_right {left right : Known} {env : Env}
    (h : propagate_KnownSound right env) : propagate_KnownSound (meet left right) env :=
  propagate_sound_of_agree (fun _ hm => (propagate_mem_meet.mp hm).2) h

/-- `known` is a loop invariant of `body`: one run from it re-establishes every one of its facts. -/
def propagate_Stable (known : Known) (body : List Stmt) : Prop :=
  ∀ entry ∈ known, (Assoc.get entry.1 (program known body).1).any (sameConstant entry.2) = true

/-- `loopInvariant` only forgets facts and stops at a loop invariant, whichever way it ends. -/
theorem propagate_loopInvariant_spec (body : List Stmt) (fuel : Nat) : ∀ known : Known,
    (∀ entry ∈ loopInvariant body fuel known, entry ∈ known) ∧
      propagate_Stable (loopInvariant body fuel known) body := by
  induction fuel with
  | zero => intro known; rw [loopInvariant]; exact ⟨by simp, by simp [propagate_Stable]⟩
  | succ fuel ih =>
    intro known
    rw [loopInvariant]
    split
    · rename_i hl
      refine ⟨fun _ h => h, ?_⟩
      intro entry hm
      exact (List.length_filter_eq_length_iff.mp hl) entry hm
    · refine ⟨fun entry hm => ?_, (ih _).2⟩
      exact (propagate_mem_meet.mp ((ih _).1 entry hm)).1

/-- The facts kept across a loop never mention a variable the body leaves unknown. -/
theorem propagate_while_drops_unknown (known : Known) (c : Exp) (body : List Stmt) (x : Bap.Var) (e : Exp)
    (hm : (x, e) ∈ (stmt known (.while c body)).1)
    (h : Assoc.get x (program (stmt known (.while c body)).1 body).1 = none) : False := by
  have hs := (propagate_loopInvariant_spec body (known.length + 1) known).2
  simp only [stmt] at hm h
  have := hs _ hm
  simp [h] at this

/-- The facts kept across a loop never disagree with what the body assigns. -/
theorem propagate_while_stable (known : Known) (c : Exp) (body : List Stmt) (x : Bap.Var) (e : Exp)
    (hm : (x, e) ∈ (stmt known (.while c body)).1) :
    (Assoc.get x (program (stmt known (.while c body)).1 body).1).any (sameConstant e) = true := by
  have hs := (propagate_loopInvariant_spec body (known.length + 1) known).2
  simp only [stmt] at hm ⊢
  exact hs _ hm

/-- After a branch only the facts both sides agree on survive. -/
theorem propagate_ifElse_known (known : Known) (c : Exp) (yes no : List Stmt) :
    (stmt known (.ifElse c yes no)).1 = meet (program known yes).1 (program known no).1 := by
  simp only [stmt]

private theorem propagate_stmt_move_sound {known : Known} {env : Env}
    (h : propagate_KnownSound known env) (v : Bap.Var) (e : Exp) (r : Value)
    (he : evalExp env e = .ok r) :
    propagate_KnownSound (stmt known (.move v e)).1 (Bil.bind env v r) := by
  simp only [stmt]
  have hs := propagate_simplify_eval known env e h
  split
  · rename_i w c hc
    intro u s hu
    simp only [Assoc.put, List.mem_cons, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | hu
    · rw [hc] at hs ⊢
      rw [he] at hs
      simp only [evalExp] at hs
      refine ⟨w, c, rfl, ?_⟩
      rw [propagate_lookup_bind]
      simp only [ite_true]
      exact hs.symm ▸ rfl
    · exact propagate_KnownSound_filter_bind h v r u s hu
  · exact propagate_KnownSound_filter_bind h v r

private theorem propagate_program_nil (known : Known) : program known [] = (known, []) := by
  simp [program]

private theorem propagate_fold_acc (code : List Stmt) (known : Known) (acc : List Stmt) :
    code.foldl (fun (current : Known × List Stmt) statement =>
        let (known, statement) := stmt current.1 statement
        (known, current.2 ++ [statement])) (known, acc) =
      ((program known code).1, acc ++ (program known code).2) := by
  induction code generalizing known acc with
  | nil => simp [program]
  | cons head tail ih =>
    simp only [program, List.foldl_cons]
    rw [ih, ih]
    simp

theorem propagate_program_cons (known : Known) (head : Stmt) (tail : List Stmt) :
    program known (head :: tail) =
      ((program (stmt known head).1 tail).1, (stmt known head).2 :: (program (stmt known head).1 tail).2) := by
  rw [program, List.foldl_cons]
  simp only [List.nil_append]
  rw [propagate_fold_acc]
  simp

private theorem propagate_ok_bind {α β ε} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

private theorem propagate_exec_cons (f : Nat) (st : State) (s : Stmt) (rest : List Stmt) :
    execProgram (f + 1) st (s :: rest) =
      execStmt f st s >>= fun r => match r.2 with
        | .normal => execProgram f r.1 rest
        | other => .ok (r.1, other) := by
  simp only [execProgram]
  cases execStmt f st s with
  | error => rfl
  | ok r => rcases r with ⟨n, e⟩; cases e <;> rfl

private theorem propagate_exec_nil (f : Nat) (st : State) : execProgram (f + 1) st [] = .ok (st, .normal) := by
  simp only [execProgram]

private theorem propagate_exec_move (f : Nat) (st : State) (v : Bap.Var) (e : Exp) :
    execStmt (f + 1) st (.move v e) =
      evalExp st.env e >>= fun r => .ok (⟨Bil.bind st.env v r⟩, .normal) := by
  simp only [execStmt, execExp]

/-- A loop step, given how its condition evaluated. -/
private def propagate_loopStep (f : Nat) (st : State) (c : Exp) (body : List Stmt) (v : Value) :
    Except String (State × Effect) :=
  Value.asBits v >>= fun bits =>
    if bits.1 = 1 then
      if bits.2.toNat = 1 then
        execProgram f st body >>= fun r => match r.2 with
          | .normal => execStmt f r.1 (.while c body)
          | other => .ok (r.1, other)
      else .ok (st, .normal)
    else .error "condition must be one bit"

private theorem propagate_exec_while (f : Nat) (st : State) (c : Exp) (body : List Stmt) :
    execStmt (f + 1) st (.while c body) =
      evalExp st.env c >>= propagate_loopStep f st c body := by
  simp only [execStmt, execExp]
  cases evalExp st.env c with
  | error => rfl
  | ok v =>
    simp only [propagate_ok_bind, propagate_loopStep]
    cases Value.asBits v with
    | error => rfl
    | ok bits =>
      rcases bits with ⟨w, cv⟩
      simp only [propagate_ok_bind]
      by_cases hw : w = 1
      · subst hw
        simp only [dite_true, ite_true]
        have hb : (cv = 1) ↔ cv.toNat = 1 := by
          constructor
          · rintro rfl; rfl
          · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
        by_cases hc : cv = 1
        · simp only [hc, ite_true, show (1 : BitVec 1).toNat = 1 from rfl]
          cases execProgram f st body with
          | error => rfl
          | ok r => rcases r with ⟨n, e⟩; cases e <;> rfl
        · simp only [hc, ite_false, show ¬ cv.toNat = 1 from fun h => hc (hb.mpr h)]
      · simp [hw]

/-- A branch, given how its condition evaluated. -/
private def propagate_branchStep (f : Nat) (st : State) (yes no : List Stmt) (v : Value) :
    Except String (State × Effect) :=
  Value.asBits v >>= fun bits =>
    if bits.1 = 1 then
      if bits.2.toNat = 1 then execProgram f st yes else execProgram f st no
    else .error "condition must be one bit"

private theorem propagate_exec_ifElse (f : Nat) (st : State) (c : Exp) (yes no : List Stmt) :
    execStmt (f + 1) st (.ifElse c yes no) =
      evalExp st.env c >>= propagate_branchStep f st yes no := by
  simp only [execStmt, execExp]
  cases evalExp st.env c with
  | error => rfl
  | ok v =>
    simp only [propagate_ok_bind, propagate_branchStep]
    cases Value.asBits v with
    | error => rfl
    | ok bits =>
      rcases bits with ⟨w, cv⟩
      simp only [propagate_ok_bind]
      by_cases hw : w = 1
      · subst hw
        have hb : (cv = 1) ↔ cv.toNat = 1 := by
          constructor
          · rintro rfl; rfl
          · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
        by_cases hc : cv = 1
        · subst hc; rfl
        · have hc' : ¬ cv = 1#1 := hc
          simp [hc', show ¬ cv.toNat = 1 from fun h => hc (hb.mpr h)]
      · simp [hw]

private def propagate_SimStmt (fuel : Nat) : Prop :=
  ∀ (s : Stmt) (known : Known) (st : State), propagate_KnownSound known st.env →
    execStmt fuel st (stmt known s).2 = execStmt fuel st s ∧
      ∀ next, execStmt fuel st s = .ok (next, .normal) →
        propagate_KnownSound (stmt known s).1 next.env

private def propagate_SimLoop (fuel : Nat) : Prop :=
  ∀ (c : Exp) (body : List Stmt) (inv : Known) (st : State),
    propagate_Stable inv body → propagate_KnownSound inv st.env →
    execStmt fuel st (.while (simplify inv c) (program inv body).2) = execStmt fuel st (.while c body) ∧
      ∀ next, execStmt fuel st (.while c body) = .ok (next, .normal) →
        propagate_KnownSound inv next.env

private def propagate_SimProgram (fuel : Nat) : Prop :=
  ∀ (code : List Stmt) (known : Known) (st : State), propagate_KnownSound known st.env →
    execProgram fuel st (program known code).2 = execProgram fuel st code ∧
      ∀ next, execProgram fuel st code = .ok (next, .normal) →
        propagate_KnownSound (program known code).1 next.env

private theorem propagate_sim (fuel : Nat) :
    propagate_SimStmt fuel ∧ propagate_SimLoop fuel ∧ propagate_SimProgram fuel := by
  induction fuel with
  | zero =>
    simp [propagate_SimStmt, propagate_SimLoop, propagate_SimProgram, execStmt, execProgram]
  | succ f ih =>
    obtain ⟨ihStmt, ihLoop, ihProgram⟩ := ih
    have loop : propagate_SimLoop (f + 1) := by
      intro c body inv st hstable hsound
      simp only [propagate_exec_while, propagate_simplify_eval inv st.env c hsound]
      cases hv : evalExp st.env c with
      | error => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
      | ok v =>
        simp only [propagate_ok_bind, propagate_loopStep]
        cases Value.asBits v with
        | error => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
        | ok bits =>
          simp only [propagate_ok_bind]
          by_cases hw : bits.1 = 1
          · simp only [hw, ite_true]
            by_cases hc : bits.2.toNat = 1
            · simp only [hc, ite_true]
              have hb := ihProgram body inv st hsound
              rw [hb.1]
              cases hr : execProgram f st body with
              | error => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
              | ok r =>
                rcases r with ⟨n, e⟩
                cases e with
                | normal =>
                  have hn := propagate_sound_of_agree hstable (hb.2 n hr)
                  exact ihLoop c body inv n hstable hn
                | jump _ => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
                | special _ => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
                | cpuExn _ => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
            · simp only [hc, ite_false]
              refine ⟨by first | rfl | trivial, fun next h => ?_⟩
              cases h
              exact hsound
          · simp only [hw, ite_false]
            exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
    have stmtStep : propagate_SimStmt (f + 1) := by
      intro s known st h
      cases s with
      | move v e =>
        constructor
        · simp only [stmt, propagate_exec_move, propagate_simplify_eval known st.env e h]
        · intro next he
          rw [propagate_exec_move] at he
          rcases propagate_bind_ok he with ⟨r, hr, he⟩
          cases he
          exact propagate_stmt_move_sound h v e r hr
      | jmp t =>
        constructor
        · simp only [stmt, execStmt, execExp, propagate_simplify_eval known st.env t h]
        · intro next he
          simp only [execStmt, execExp] at he
          rcases propagate_bind_ok he with ⟨r, _, he⟩
          rcases propagate_bind_ok he with ⟨b, _, he⟩
          cases he
      | special m =>
        refine ⟨by simp only [stmt], ?_⟩
        intro next he
        simp only [execStmt] at he
        cases he
      | cpuExn m =>
        refine ⟨by simp only [stmt], ?_⟩
        intro next he
        simp only [execStmt] at he
        cases he
      | «while» c body =>
        have hspec := propagate_loopInvariant_spec body (known.length + 1) known
        have hsound : propagate_KnownSound (loopInvariant body (known.length + 1) known) st.env :=
          fun v r hm => h v r (hspec.1 _ hm)
        simp only [stmt]
        exact loop c body _ st hspec.2 hsound
      | ifElse c yes no =>
        simp only [stmt, propagate_exec_ifElse, propagate_simplify_eval known st.env c h]
        cases evalExp st.env c with
        | error => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
        | ok v =>
          simp only [propagate_ok_bind, propagate_branchStep]
          cases Value.asBits v with
          | error => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
          | ok bits =>
            simp only [propagate_ok_bind]
            by_cases hw : bits.1 = 1
            · simp only [hw, ite_true]
              by_cases hc : bits.2.toNat = 1
              · simp only [hc, ite_true]
                have hb := ihProgram yes known st h
                exact ⟨hb.1, fun next hn => propagate_meet_sound_left (hb.2 next hn)⟩
              · simp only [hc, ite_false]
                have hb := ihProgram no known st h
                exact ⟨hb.1, fun next hn => propagate_meet_sound_right (hb.2 next hn)⟩
            · simp only [hw, ite_false]
              exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
    refine ⟨stmtStep, loop, ?_⟩
    intro code known st h
    cases code with
    | nil =>
      simp only [propagate_program_nil, propagate_exec_nil]
      exact ⟨by first | rfl | trivial, fun next he => by cases he; exact h⟩
    | cons head tail =>
      rw [propagate_program_cons]
      simp only [propagate_exec_cons]
      have hh := ihStmt head known st h
      rw [hh.1]
      cases hr : execStmt f st head with
      | error => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
      | ok r =>
        rcases r with ⟨next, effect⟩
        cases effect with
        | normal =>
          exact ihProgram tail _ next (hh.2 next hr)
        | jump _ => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
        | special _ => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩
        | cpuExn _ => exact ⟨by first | rfl | trivial, fun _ h => by cases h⟩

/-- Simulation for every program: the propagated code behaves exactly like the original under
every fuel and every state consistent with the known constants, errors included, and a normal
exit leaves the constants it reports true. -/
theorem propagate_program_sim (fuel : Nat) (code : List Stmt) (known : Known) (st : State)
    (h : propagate_KnownSound known st.env) :
    execProgram fuel st (program known code).2 = execProgram fuel st code ∧
      ∀ next, execProgram fuel st code = .ok (next, .normal) →
        propagate_KnownSound (program known code).1 next.env :=
  (propagate_sim fuel).2.2 code known st h

theorem propagate_stmt_sim (fuel : Nat) (s : Stmt) (known : Known) (st : State)
    (h : propagate_KnownSound known st.env) :
    execStmt fuel st (stmt known s).2 = execStmt fuel st s ∧
      ∀ next, execStmt fuel st s = .ok (next, .normal) →
        propagate_KnownSound (stmt known s).1 next.env :=
  (propagate_sim fuel).1 s known st h

/-- Whole-program correctness of `propagate`, for every program, state and fuel. -/
theorem propagate_run (code : Bil.Program) (st : State) (fuel : Nat) :
    run (propagate code) st fuel = run code st fuel :=
  (propagate_program_sim fuel code [] st (propagate_KnownSound_empty _)).1

/-- Regression: a constant reassigned in a branch is not used after it. `y := x` stays as written,
and `propagate_run` shows the result equals the original's. -/
theorem propagate_branch_not_stale (x y : Bap.Var) {w} (a b : BitVec w) (hab : a ≠ b) :
    (program [] [.move x (.int a), .ifElse (.int (1 : BitVec 1)) [.move x (.int b)] [], .move y (.var x)]).2.getLast? =
      some (.move y (.var x)) := by
  have hfold : ∀ {w} (v : BitVec w), foldExp (.int v) = .int v := fun v => by
    rw [foldExp_of_eval_bits (value := v)]; rfl
  have hint : ∀ (known : Known) {w} (v : BitVec w), simplify known (.int v) = .int v := fun known _ v => by
    simp [simplify, substitute, hfold]
  have hvar : foldExp (.var x) = .var x := by
    rw [foldExp]; simp [evalExp, lookup]
  have hne : a.toNat ≠ b.toNat := fun h => hab (BitVec.eq_of_toNat_eq h)
  have hs : simplify [] (.var x) = .var x := by simp [simplify, substitute, hvar]
  have hmeet : meet [(x, .int b)] [(x, .int a)] = [] := by
    simp [meet, Assoc.get, sameConstant, hne.symm]
  simp [propagate_program_cons, propagate_program_nil, stmt, hint, hs, hmeet, Assoc.put]

/-- `propagate` keeps the program's shape: one output statement per input statement. -/
theorem propagate_length (code : List Stmt) (known : Known) : (program known code).2.length = code.length := by
  induction code generalizing known with
  | nil => simp [propagate_program_nil]
  | cons head tail ih => simp [propagate_program_cons, ih]

end Propagate

section DeadCode

set_option linter.unusedSimpArgs false

open Bap.Bil
open Bap.Analysis.DeadCode
open_private Bap.Analysis.DeadCode in Bap.Analysis.DeadCode : addVars removeVar reads stmtLive loopLive program
open_private Bap.Bil.Transform in Bap.Bil : union freeVarsExp

/-- Memory-typed variables, whose moves are always kept. -/
def deadcode_isMem : Typ → Bool
  | .mem _ _ => true
  | _ => false

/-- The statements the pass deletes given the set of variables live after them. -/
def deadcode_dropped (l : List Bap.Var) : Stmt → Bool
  | .move v _ => !deadcode_isMem v.typ && !l.contains v
  | _ => false

theorem deadcode_dropped_iff (l : List Bap.Var) (s : Stmt) :
    deadcode_dropped l s = true ↔
      ∃ v e, s = .move v e ∧ deadcode_isMem v.typ = false ∧ v ∉ l := by
  cases s <;> simp [deadcode_dropped]

theorem deadcode_mem_addVars (l r : List Bap.Var) (v : Bap.Var) :
    v ∈ addVars l r ↔ v ∈ l ∨ v ∈ r := by
  simp [addVars, List.mem_eraseDups]

theorem deadcode_mem_removeVar (l : List Bap.Var) (v w : Bap.Var) :
    w ∈ removeVar l v ↔ w ∈ l ∧ w ≠ v := by
  simp [removeVar]

variable (o : List Bap.Var)

private theorem deadcode_move_dead {l : List Bap.Var} {v : Bap.Var} (e : Exp)
    (hm : deadcode_isMem v.typ = false) (h : v ∉ l) :
    stmtLive o l (.move v e) = (l, none) := by
  cases ht : v.typ <;> simp_all [stmtLive, deadcode_isMem]

private theorem deadcode_move_live {l : List Bap.Var} {v : Bap.Var} (e : Exp)
    (hm : deadcode_isMem v.typ = false) (h : v ∈ l) :
    stmtLive o l (.move v e) = (addVars (removeVar l v) (freeVars e), some (.move v e)) := by
  cases ht : v.typ <;> simp_all [stmtLive, deadcode_isMem]

private theorem deadcode_move_mem {l : List Bap.Var} {v : Bap.Var} (e : Exp)
    (hm : deadcode_isMem v.typ = true) :
    stmtLive o l (.move v e) = (addVars l (freeVars e), some (.move v e)) := by
  cases ht : v.typ <;> simp_all [stmtLive, deadcode_isMem]

/-- What is live before a jump is what the program's exit needs, not what follows the jump. -/
theorem deadcode_stmtLive_jmp (l : List Bap.Var) (t : Exp) :
    stmtLive o l (.jmp t) = (addVars o (freeVars t), some (.jmp t)) := by
  simp [stmtLive]

theorem deadcode_stmtLive_special (l : List Bap.Var) (m : String) :
    stmtLive o l (.special m) = (o, some (.special m)) := by
  simp [stmtLive]

theorem deadcode_stmtLive_cpuExn (l : List Bap.Var) (n : Nat) :
    stmtLive o l (.cpuExn n) = (o, some (.cpuExn n)) := by
  simp [stmtLive]

/-- Liveness at the head of a loop. -/
private def deadcode_head (l : List Bap.Var) (c : Exp) (body : List Stmt) : List Bap.Var :=
  loopLive o body ((body.flatMap reads ++ o ++ addVars l (freeVars c)).eraseDups.length + 1)
    (addVars l (freeVars c))

private theorem deadcode_stmtLive_while (l : List Bap.Var) (c : Exp) (body : List Stmt) :
    stmtLive o l (.while c body) =
      (deadcode_head o l c body, some (.while c (program o (deadcode_head o l c body) body).2)) := by
  simp only [stmtLive, deadcode_head]

private theorem deadcode_stmtLive_ifElse (l : List Bap.Var) (c : Exp) (yes no : List Stmt) :
    stmtLive o l (.ifElse c yes no) =
      (addVars (freeVars c) ((program o l yes).1 ++ (program o l no).1),
        some (.ifElse c (program o l yes).2 (program o l no).2)) := by
  simp only [stmtLive]

/-- A statement disappears exactly when it is a non-memory move to a variable dead after it, and
then liveness passes through it unchanged. -/
theorem deadcode_stmtLive_none_iff (l : List Bap.Var) (s : Stmt) :
    (stmtLive o l s).2 = none ↔ deadcode_dropped l s = true := by
  cases s with
  | move v e =>
    cases hm : deadcode_isMem v.typ with
    | true => simp [deadcode_move_mem o e hm, deadcode_dropped, hm]
    | false =>
      by_cases h : v ∈ l
      · simp [deadcode_move_live o e hm h, deadcode_dropped, hm, h]
      · simp [deadcode_move_dead o e hm h, deadcode_dropped, hm, h]
  | jmp _ => simp [deadcode_stmtLive_jmp, deadcode_dropped]
  | special _ => simp [deadcode_stmtLive_special, deadcode_dropped]
  | cpuExn _ => simp [deadcode_stmtLive_cpuExn, deadcode_dropped]
  | «while» _ _ => simp [deadcode_stmtLive_while, deadcode_dropped]
  | ifElse _ _ _ => simp [deadcode_stmtLive_ifElse, deadcode_dropped]

private theorem deadcode_stmtLive_none {l : List Bap.Var} {s : Stmt} (h : (stmtLive o l s).2 = none) :
    (stmtLive o l s).1 = l := by
  rcases (deadcode_dropped_iff l s).mp ((deadcode_stmtLive_none_iff o l s).mp h) with ⟨v, e, rfl, hm, hv⟩
  simp [deadcode_move_dead o e hm hv]

theorem deadcode_program_nil (live : List Bap.Var) : program o live [] = (live, []) := by
  simp [program]

theorem deadcode_program_cons (live : List Bap.Var) (head : Stmt) (tail : List Stmt) :
    program o live (head :: tail) =
      ((stmtLive o (program o live tail).1 head).1,
        (stmtLive o (program o live tail).1 head).2.toList ++ (program o live tail).2) := by
  rw [program, program, List.reverse_cons, List.foldl_append]
  rfl

/-- Backward composition: the suffix is processed first and its live set feeds the prefix. -/
theorem deadcode_program_append (live : List Bap.Var) (pre post : List Stmt) :
    program o live (pre ++ post) =
      ((program o (program o live post).1 pre).1,
        (program o (program o live post).1 pre).2 ++ (program o live post).2) := by
  induction pre with
  | nil => simp [deadcode_program_nil]
  | cons head tail ih =>
    simp only [List.cons_append, deadcode_program_cons, ih, List.append_assoc]

mutual
  /-- `opt` is `s` with its child blocks optimized: same statement otherwise. -/
  inductive deadcode_EmbedsStmt : Stmt → Stmt → Prop
    | same (s : Stmt) : deadcode_EmbedsStmt s s
    | «while» (c : Exp) {opt code : List Stmt} :
        deadcode_Embeds opt code → deadcode_EmbedsStmt (.while c opt) (.while c code)
    | ifElse (c : Exp) {y y' n n' : List Stmt} :
        deadcode_Embeds y' y → deadcode_Embeds n' n →
        deadcode_EmbedsStmt (.ifElse c y' n') (.ifElse c y n)

  /-- `opt` arises from `code` by deleting non-memory moves only, at any nesting depth; nothing is
  added, reordered or changed. -/
  inductive deadcode_Embeds : List Stmt → List Stmt → Prop
    | nil : deadcode_Embeds [] []
    | drop (v : Bap.Var) (e : Exp) {opt code : List Stmt} :
        deadcode_isMem v.typ = false → deadcode_Embeds opt code →
        deadcode_Embeds opt (.move v e :: code)
    | keep {t s : Stmt} {opt code : List Stmt} :
        deadcode_EmbedsStmt t s → deadcode_Embeds opt code →
        deadcode_Embeds (t :: opt) (s :: code)
end

private theorem deadcode_program_embeds_of {code : List Stmt}
    (hs : ∀ s ∈ code, ∀ l t, (stmtLive o l s).2 = some t → deadcode_EmbedsStmt t s) (l : List Bap.Var) :
    deadcode_Embeds (program o l code).2 code := by
  induction code with
  | nil => simp only [deadcode_program_nil]; exact .nil
  | cons head tail ih =>
    have ih := ih fun s hm => hs s (List.mem_cons_of_mem _ hm)
    rw [deadcode_program_cons]
    cases h : (stmtLive o (program o l tail).1 head).2 with
    | none =>
      rcases (deadcode_dropped_iff _ head).mp ((deadcode_stmtLive_none_iff o _ head).mp h) with ⟨v, e, rfl, hm, _⟩
      exact .drop v e hm ih
    | some t =>
      exact .keep (hs head (by simp) _ _ h) ih

private theorem deadcode_stmt_embeds (s : Stmt) : ∀ l t, (stmtLive o l s).2 = some t → deadcode_EmbedsStmt t s := by
  induction s using stmtInduction with
  | move v e =>
    intro l t h
    cases hm : deadcode_isMem v.typ with
    | true => rw [deadcode_move_mem o e hm] at h; cases h; exact .same _
    | false =>
      by_cases hv : v ∈ l
      · rw [deadcode_move_live o e hm hv] at h; cases h; exact .same _
      · rw [deadcode_move_dead o e hm hv] at h; cases h
  | jmp t => intro l t' h; rw [deadcode_stmtLive_jmp] at h; cases h; exact .same _
  | special m => intro l t h; rw [deadcode_stmtLive_special] at h; cases h; exact .same _
  | cpuExn n => intro l t h; rw [deadcode_stmtLive_cpuExn] at h; cases h; exact .same _
  | while_ c body ih =>
    intro l t h
    rw [deadcode_stmtLive_while] at h
    cases h
    exact .while c (deadcode_program_embeds_of o ih _)
  | ifElse c yes no iy in_ =>
    intro l t h
    rw [deadcode_stmtLive_ifElse] at h
    cases h
    exact .ifElse c (deadcode_program_embeds_of o iy _) (deadcode_program_embeds_of o in_ _)

/-- Optimization only deletes non-memory moves, at any depth. -/
theorem deadcode_optimize_embeds (code : Bil.Program) : deadcode_Embeds (optimize o code) code :=
  deadcode_program_embeds_of o (fun s _ => deadcode_stmt_embeds o s) o

/-- Local specification at any position: the output around a statement is the output of its
context, and the statement is dropped iff it is a dead move given the liveness of its suffix. -/
theorem deadcode_optimize_split (pre post : Bil.Program) (s : Stmt) :
    optimize o (pre ++ s :: post) =
      (program o (stmtLive o (program o o post).1 s).1 pre).2 ++
        (stmtLive o (program o o post).1 s).2.toList ++ optimize o post := by
  show (program o o (pre ++ s :: post)).2 = _
  rw [deadcode_program_append, deadcode_program_cons]
  simp only [List.append_assoc]
  rfl

/-- A definition of a variable that is live after it is never removed. -/
theorem deadcode_keeps_live_def (pre post : Bil.Program) (v : Bap.Var) (e : Exp)
    (h : v ∈ (program o o post).1) :
    .move v e ∈ optimize o (pre ++ .move v e :: post) := by
  rw [deadcode_optimize_split]
  cases hm : deadcode_isMem v.typ with
  | true => simp [deadcode_move_mem o e hm]
  | false => simp [deadcode_move_live o e hm h]

/-- Outputs are live at the end of the program, so the final write to an output survives. -/
theorem deadcode_keeps_final_output (pre : Bil.Program) (v : Bap.Var) (e : Exp)
    (h : v ∈ o) : .move v e ∈ optimize o (pre ++ [.move v e]) := by
  apply deadcode_keeps_live_def
  simpa [deadcode_program_nil] using h

private theorem deadcode_addVars_subset {l r U : List Bap.Var} (hl : l ⊆ U) (hr : r ⊆ U) :
    addVars l r ⊆ U := by
  intro v hv
  rcases (deadcode_mem_addVars l r v).mp hv with h | h
  · exact hl h
  · exact hr h

private theorem deadcode_reads_flat {code : List Stmt} {U : List Bap.Var} (h : code.flatMap reads ⊆ U)
    {s : Stmt} (hs : s ∈ code) : reads s ⊆ U :=
  fun _ hv => h (List.mem_flatMap.mpr ⟨s, hs, hv⟩)

/-- Everything live before `code` is the live set after it, an output, or something `code` reads. -/
private theorem deadcode_program_closed {code : List Stmt}
    (hs : ∀ s ∈ code, ∀ L U, L ⊆ U → o ⊆ U → reads s ⊆ U → (stmtLive o L s).1 ⊆ U)
    {L U : List Bap.Var} (hL : L ⊆ U) (ho : o ⊆ U) (hr : code.flatMap reads ⊆ U) :
    (program o L code).1 ⊆ U := by
  induction code with
  | nil => simpa [deadcode_program_nil] using hL
  | cons head tail ih =>
    rw [deadcode_program_cons]
    exact hs head (by simp) _ _
      (ih (fun s hm => hs s (List.mem_cons_of_mem _ hm))
        (deadcode_reads_flat_tail hr)) ho (deadcode_reads_flat hr (by simp))
where deadcode_reads_flat_tail {head tail} {U : List Bap.Var} (h : (head :: tail).flatMap reads ⊆ U) :
    tail.flatMap reads ⊆ U := fun _ hv => h (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hv)

private theorem deadcode_loopLive_closed {body : List Stmt}
    (hs : ∀ s ∈ body, ∀ L U, L ⊆ U → o ⊆ U → reads s ⊆ U → (stmtLive o L s).1 ⊆ U)
    {U : List Bap.Var} (ho : o ⊆ U) (hr : body.flatMap reads ⊆ U) (fuel : Nat) :
    ∀ current, current ⊆ U → loopLive o body fuel current ⊆ U := by
  induction fuel with
  | zero =>
    intro current hc
    rw [loopLive]
    exact deadcode_addVars_subset hc (List.append_subset.mpr ⟨hr, ho⟩)
  | succ fuel ih =>
    intro current hc
    rw [loopLive]
    split
    · exact hc
    · exact ih _ (deadcode_addVars_subset hc (deadcode_program_closed o hs hc ho hr))

private theorem deadcode_stmt_closed (s : Stmt) :
    ∀ L U, L ⊆ U → o ⊆ U → reads s ⊆ U → (stmtLive o L s).1 ⊆ U := by
  induction s using stmtInduction with
  | move v e =>
    intro L U hL _ hr
    simp only [reads] at hr
    cases hm : deadcode_isMem v.typ with
    | true =>
      rw [deadcode_move_mem o e hm]
      exact deadcode_addVars_subset hL hr
    | false =>
      by_cases hv : v ∈ L
      · rw [deadcode_move_live o e hm hv]
        refine deadcode_addVars_subset (fun w hw => hL ((deadcode_mem_removeVar L v w).mp hw).1) hr
      · rw [deadcode_move_dead o e hm hv]; exact hL
  | jmp t =>
    intro L U _ ho hr
    simp only [reads] at hr
    rw [deadcode_stmtLive_jmp]
    exact deadcode_addVars_subset ho hr
  | special m => intro L U _ ho _; rw [deadcode_stmtLive_special]; exact ho
  | cpuExn n => intro L U _ ho _; rw [deadcode_stmtLive_cpuExn]; exact ho
  | while_ c body ih =>
    intro L U hL ho hr
    simp only [reads, List.append_subset] at hr
    rw [deadcode_stmtLive_while]
    exact deadcode_loopLive_closed o ih ho hr.2 _ _ (deadcode_addVars_subset hL hr.1)
  | ifElse c yes no iy in_ =>
    intro L U hL ho hr
    simp only [reads, List.append_subset] at hr
    rw [deadcode_stmtLive_ifElse]
    exact deadcode_addVars_subset hr.1.1 (List.append_subset.mpr
      ⟨deadcode_program_closed o iy hL ho hr.1.2, deadcode_program_closed o in_ hL ho hr.2⟩)

/-- `loopLive` stops above where it started, at a set closed under one run of the body. -/
theorem deadcode_loopLive_spec (body : List Stmt) (fuel : Nat) : ∀ current : List Bap.Var,
    current ⊆ loopLive o body fuel current ∧
      (program o (loopLive o body fuel current) body).1 ⊆ loopLive o body fuel current := by
  induction fuel with
  | zero =>
    intro current
    have hrw : loopLive o body 0 current = addVars current (body.flatMap reads ++ o) := by rw [loopLive]
    rw [hrw]
    have hsub : current ⊆ addVars current (body.flatMap reads ++ o) :=
      fun v hv => (deadcode_mem_addVars _ _ v).mpr (Or.inl hv)
    have hall : body.flatMap reads ++ o ⊆ addVars current (body.flatMap reads ++ o) :=
      fun v hv => (deadcode_mem_addVars _ _ v).mpr (Or.inr hv)
    refine ⟨hsub, ?_⟩
    exact deadcode_program_closed o (fun s _ => deadcode_stmt_closed o s) (fun _ h => h)
      (fun _ hv => hall (List.mem_append_right _ hv))
      (fun _ hv => hall (List.mem_append_left _ hv))
  | succ fuel ih =>
    intro current
    by_cases h : (program o current body).1.all current.contains = true
    · have hrw : loopLive o body (fuel + 1) current = current := by rw [loopLive]; simp [h]
      rw [hrw]
      refine ⟨fun _ h => h, fun v hv => ?_⟩
      have := List.all_eq_true.mp h v hv
      simpa using this
    · have hrw : loopLive o body (fuel + 1) current =
          loopLive o body fuel (addVars current (program o current body).1) := by
        rw [loopLive]
        simp only [Bool.not_eq_true] at h
        simp [h]
      rw [hrw]
      refine ⟨fun v hv => (ih _).1 ((deadcode_mem_addVars _ _ v).mpr (Or.inl hv)), (ih _).2⟩

/-- The set live before a loop holds what is live after it and the condition's variables, and one
more run of the body needs nothing beyond it. -/
theorem deadcode_while_head (l : List Bap.Var) (c : Exp) (body : List Stmt) :
    l ⊆ (stmtLive o l (.while c body)).1 ∧ freeVars c ⊆ (stmtLive o l (.while c body)).1 ∧
      (program o (stmtLive o l (.while c body)).1 body).1 ⊆ (stmtLive o l (.while c body)).1 := by
  rw [deadcode_stmtLive_while]
  have h := deadcode_loopLive_spec o body
    ((body.flatMap reads ++ o ++ addVars l (freeVars c)).eraseDups.length + 1) (addVars l (freeVars c))
  exact ⟨fun v hv => h.1 ((deadcode_mem_addVars _ _ v).mpr (Or.inl hv)),
    fun v hv => h.1 ((deadcode_mem_addVars _ _ v).mpr (Or.inr hv)), h.2⟩

private theorem deadcode_mem_union (l r : List Bap.Var) (v : Bap.Var) :
    v ∈ union l r ↔ v ∈ l ∨ v ∈ r := by
  simp [union, List.mem_eraseDups]

private theorem deadcode_eval_agree_aux (e : Exp) : ∀ (bound : List Bap.Var) (a b : Env),
    (∀ w, w ∈ freeVarsExp bound e ∨ w ∈ bound → lookup a w = lookup b w) →
    evalExp a e = evalExp b e := by
  induction e with
  | int _ => intros; rfl
  | var v =>
    intro bound a b h
    simp only [evalExp]
    apply h
    by_cases hv : v ∈ bound
    · exact Or.inr hv
    · simp [freeVarsExp, hv]
  | load _ _ _ _ im ia =>
    intro bound a b h
    simp only [evalExp,
      im bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      ia bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw])]
  | store _ _ _ _ _ im ia iv =>
    intro bound a b h
    simp only [evalExp,
      im bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      ia bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      iv bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw])]
  | bin _ _ _ il ir =>
    intro bound a b h
    simp only [evalExp,
      il bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      ir bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw])]
  | concat _ _ il ir =>
    intro bound a b h
    simp only [evalExp,
      il bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      ir bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw])]
  | un _ _ i =>
    intro bound a b h
    simp only [evalExp, i bound a b fun w hw => h w (by simpa [freeVarsExp] using hw)]
  | cast _ _ _ i =>
    intro bound a b h
    simp only [evalExp, i bound a b fun w hw => h w (by simpa [freeVarsExp] using hw)]
  | extract _ _ _ i =>
    intro bound a b h
    simp only [evalExp, i bound a b fun w hw => h w (by simpa [freeVarsExp] using hw)]
  | letIn v _ _ il ib =>
    intro bound a b h
    simp only [evalExp,
      il bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw])]
    congr 1
    funext r
    apply ib (v :: bound)
    intro w hw
    rw [propagate_lookup_bind, propagate_lookup_bind]
    by_cases hv : w = v
    · simp [hv]
    · simp only [hv, ite_false]
      apply h
      rcases hw with hw | hw
      · exact Or.inl (by simp [freeVarsExp, deadcode_mem_union, hw])
      · exact Or.inr (by simpa [hv] using hw)
  | ite _ _ _ ic iy in_ =>
    intro bound a b h
    simp only [evalExp,
      ic bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      iy bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw]),
      in_ bound a b fun w hw => h w (by rcases hw with hw | hw <;> simp [freeVarsExp, deadcode_mem_union, hw])]
  | unknown _ _ => intros; rfl

/-- Evaluation depends only on the free variables. -/
theorem deadcode_eval_agree (e : Exp) (a b : Env) (h : ∀ w ∈ freeVars e, lookup a w = lookup b w) :
    evalExp a e = evalExp b e :=
  deadcode_eval_agree_aux e [] a b fun w hw => by
    rcases hw with hw | hw
    · exact h w hw
    · simp at hw

/-- Two environments agree on the variables in `l`. -/
def deadcode_Agree (l : List Bap.Var) (a b : Env) : Prop := ∀ w ∈ l, lookup a w = lookup b w

/-- What must agree after an exit with effect `e`: `live` if execution continues, else `outputs`. -/
def deadcode_Post (outputs live : List Bap.Var) : Effect → Env → Env → Prop
  | .normal, a, b => deadcode_Agree live a b
  | _, a, b => deadcode_Agree outputs a b

private theorem deadcode_Agree_bind {l : List Bap.Var} {a b : Env} (v : Bap.Var) (r : Value)
    (h : ∀ w ∈ l, w ≠ v → lookup a w = lookup b w) : deadcode_Agree l (Bil.bind a v r) (Bil.bind b v r) := by
  intro w hw
  rw [propagate_lookup_bind, propagate_lookup_bind]
  by_cases hv : w = v
  · simp [hv]
  · simp [hv, h w hw hv]

private theorem deadcode_exec_fuel_succ (f : Nat) :
    (∀ st s r, execStmt f st s = .ok r → execStmt (f + 1) st s = .ok r) ∧
      (∀ st code r, execProgram f st code = .ok r → execProgram (f + 1) st code = .ok r) := by
  induction f with
  | zero => simp [execStmt, execProgram]
  | succ f ih =>
    obtain ⟨ihS, ihP⟩ := ih
    constructor
    · intro st s r h
      cases s with
      | move v e => simpa only [propagate_exec_move] using h
      | jmp t => simpa only [execStmt] using h
      | special m => simpa only [execStmt] using h
      | cpuExn n => simpa only [execStmt] using h
      | «while» c body =>
        rw [propagate_exec_while] at h ⊢
        rcases propagate_bind_ok h with ⟨v, hv, h⟩
        rw [hv]
        simp only [propagate_ok_bind]
        simp only [propagate_loopStep] at h ⊢
        rcases propagate_bind_ok h with ⟨bits, hb, h⟩
        rw [hb]
        simp only [propagate_ok_bind] at h ⊢
        split at h
        · rename_i hw
          simp only [hw, ite_true]
          split at h
          · rename_i hc
            simp only [hc, ite_true]
            rcases propagate_bind_ok h with ⟨⟨n, e⟩, hr, h⟩
            rw [ihP _ _ _ hr]
            simp only [propagate_ok_bind]
            cases e with
            | normal => exact ihS _ _ _ h
            | jump _ => exact h
            | special _ => exact h
            | cpuExn _ => exact h
          · rename_i hc
            simpa only [hc, ite_false] using h
        · cases h
      | ifElse c yes no =>
        rw [propagate_exec_ifElse] at h ⊢
        rcases propagate_bind_ok h with ⟨v, hv, h⟩
        rw [hv]
        simp only [propagate_ok_bind]
        simp only [propagate_branchStep] at h ⊢
        rcases propagate_bind_ok h with ⟨bits, hb, h⟩
        rw [hb]
        simp only [propagate_ok_bind] at h ⊢
        split at h
        · rename_i hw
          simp only [hw, ite_true]
          split at h
          · rename_i hc
            simp only [hc, ite_true]
            exact ihP _ _ _ h
          · rename_i hc
            simp only [hc, ite_false]
            exact ihP _ _ _ h
        · cases h
    · intro st code r h
      cases code with
      | nil => simpa only [propagate_exec_nil] using h
      | cons head tail =>
        rw [propagate_exec_cons] at h ⊢
        rcases propagate_bind_ok h with ⟨⟨n, e⟩, hr, h⟩
        rw [ihS _ _ _ hr]
        simp only [propagate_ok_bind]
        cases e with
        | normal => exact ihP _ _ _ h
        | jump _ => exact h
        | special _ => exact h
        | cpuExn _ => exact h

/-- More fuel never changes a successful run. -/
theorem deadcode_execProgram_fuel_mono {f g : Nat} (hfg : f ≤ g) (st : State) (code : List Stmt)
    {r : State × Effect} (h : execProgram f st code = .ok r) : execProgram g st code = .ok r := by
  induction hfg with
  | refl => exact h
  | step _ ih => exact (deadcode_exec_fuel_succ _).2 _ _ _ ih

theorem deadcode_execStmt_fuel_mono {f g : Nat} (hfg : f ≤ g) (st : State) (s : Stmt)
    {r : State × Effect} (h : execStmt f st s = .ok r) : execStmt g st s = .ok r := by
  induction hfg with
  | refl => exact h
  | step _ ih => exact (deadcode_exec_fuel_succ _).1 _ _ _ ih

private def deadcode_SimProgram (fuel : Nat) : Prop :=
  ∀ (code : List Stmt) (live : List Bap.Var) (st st' next : State) (eff : Effect),
    deadcode_Agree (program o live code).1 st.env st'.env →
    execProgram fuel st code = .ok (next, eff) →
    ∃ next', execProgram fuel st' (program o live code).2 = .ok (next', eff) ∧
      deadcode_Post o live eff next.env next'.env

private def deadcode_SimLoop (fuel : Nat) : Prop :=
  ∀ (c : Exp) (body : List Stmt) (head : List Bap.Var) (st st' next : State) (eff : Effect),
    freeVars c ⊆ head → (program o head body).1 ⊆ head → deadcode_Agree head st.env st'.env →
    execStmt fuel st (.while c body) = .ok (next, eff) →
    ∃ next', execStmt fuel st' (.while c (program o head body).2) = .ok (next', eff) ∧
      deadcode_Post o head eff next.env next'.env

private def deadcode_SimStmt (fuel : Nat) : Prop :=
  ∀ (s : Stmt) (live : List Bap.Var) (st st' next : State) (eff : Effect),
    deadcode_Agree (stmtLive o live s).1 st.env st'.env →
    execStmt fuel st s = .ok (next, eff) →
    match (stmtLive o live s).2 with
    | none => deadcode_Post o live .normal next.env st'.env ∧ (eff matches .normal)
    | some t => ∃ next', execStmt fuel st' t = .ok (next', eff) ∧ deadcode_Post o live eff next.env next'.env

private theorem deadcode_sim_eval {l : List Bap.Var} {st st' : State} {e : Exp}
    (h : deadcode_Agree l st.env st'.env) (hs : freeVars e ⊆ l) : evalExp st.env e = evalExp st'.env e :=
  deadcode_eval_agree e _ _ fun w hw => h w (hs hw)

private theorem deadcode_sim (fuel : Nat) :
    deadcode_SimStmt o fuel ∧ deadcode_SimLoop o fuel ∧ deadcode_SimProgram o fuel := by
  induction fuel with
  | zero =>
    simp [deadcode_SimStmt, deadcode_SimLoop, deadcode_SimProgram, execStmt, execProgram]
  | succ f ih =>
    obtain ⟨ihS, ihL, ihP⟩ := ih
    have loop : deadcode_SimLoop o (f + 1) := by
      intro c body head st st' next eff hc hb ha h
      rw [propagate_exec_while] at h ⊢
      rw [← deadcode_sim_eval ha hc]
      rcases propagate_bind_ok h with ⟨v, hv, h⟩
      rw [hv]
      simp only [propagate_ok_bind]
      simp only [propagate_loopStep] at h ⊢
      rcases propagate_bind_ok h with ⟨bits, hbits, h⟩
      rw [hbits]
      simp only [propagate_ok_bind] at h ⊢
      split at h
      · rename_i hw
        simp only [hw, ite_true]
        split at h
        · rename_i hcv
          simp only [hcv, ite_true]
          rcases propagate_bind_ok h with ⟨⟨n, e⟩, hr, h⟩
          obtain ⟨n', hr', hpost⟩ := ihP body head st st' n e (fun w hw => ha w (hb hw)) hr
          rw [hr']
          simp only [propagate_ok_bind]
          cases e with
          | normal => exact ihL c body head n n' next eff hc hb hpost h
          | jump _ => cases h; exact ⟨n', rfl, hpost⟩
          | special _ => cases h; exact ⟨n', rfl, hpost⟩
          | cpuExn _ => cases h; exact ⟨n', rfl, hpost⟩
        · rename_i hcv
          simp only [hcv, ite_false] at h ⊢
          cases h
          exact ⟨st', rfl, ha⟩
      · cases h
    have stmtStep : deadcode_SimStmt o (f + 1) := by
      intro s live st st' next eff ha h
      cases s with
      | move v e =>
        rw [propagate_exec_move] at h
        rcases propagate_bind_ok h with ⟨r, hr, h⟩
        cases h
        cases hm : deadcode_isMem v.typ with
        | true =>
          rw [deadcode_move_mem o e hm] at ha ⊢
          have he := deadcode_sim_eval (st' := st') (e := e) ha
            (fun w hw => (deadcode_mem_addVars _ _ w).mpr (Or.inr hw))
          refine ⟨⟨Bil.bind st'.env v r⟩, ?_, ?_⟩
          · rw [propagate_exec_move, ← he, hr]; rfl
          · exact deadcode_Agree_bind v r fun w hw _ =>
              ha w ((deadcode_mem_addVars _ _ w).mpr (Or.inl hw))
        | false =>
          by_cases hv : v ∈ live
          · rw [deadcode_move_live o e hm hv] at ha ⊢
            have he := deadcode_sim_eval (st' := st') (e := e) ha
              (fun w hw => (deadcode_mem_addVars _ _ w).mpr (Or.inr hw))
            refine ⟨⟨Bil.bind st'.env v r⟩, ?_, ?_⟩
            · rw [propagate_exec_move, ← he, hr]; rfl
            · exact deadcode_Agree_bind v r fun w hw hne =>
                ha w ((deadcode_mem_addVars _ _ w).mpr
                  (Or.inl ((deadcode_mem_removeVar _ _ _).mpr ⟨hw, hne⟩)))
          · rw [deadcode_move_dead o e hm hv] at ha ⊢
            refine ⟨?_, rfl⟩
            intro w hw
            have hne : w ≠ v := fun hc => hv (hc ▸ hw)
            rw [propagate_lookup_bind]
            simp [hne, ha w hw]
      | jmp t =>
        rw [deadcode_stmtLive_jmp] at ha ⊢
        simp only [execStmt, execExp] at h ⊢
        rw [← deadcode_sim_eval ha (fun w hw => (deadcode_mem_addVars _ _ w).mpr (Or.inr hw))]
        rcases propagate_bind_ok h with ⟨v, hv, h⟩
        rw [hv]
        simp only [propagate_ok_bind] at h ⊢
        rcases propagate_bind_ok h with ⟨b, hb, h⟩
        rw [hb]
        simp only [propagate_ok_bind] at h ⊢
        cases h
        exact ⟨st', rfl, fun w hw => ha w ((deadcode_mem_addVars _ _ w).mpr (Or.inl hw))⟩
      | special m =>
        rw [deadcode_stmtLive_special] at ha ⊢
        simp only [execStmt] at h ⊢
        cases h
        exact ⟨st', rfl, ha⟩
      | cpuExn n =>
        rw [deadcode_stmtLive_cpuExn] at ha ⊢
        simp only [execStmt] at h ⊢
        cases h
        exact ⟨st', rfl, ha⟩
      | «while» c body =>
        have hhead := deadcode_while_head o live c body
        rw [deadcode_stmtLive_while] at ha hhead ⊢
        obtain ⟨n', hn, hpost⟩ := loop c body _ st st' next eff hhead.2.1 hhead.2.2 ha h
        refine ⟨n', hn, ?_⟩
        cases eff with
        | normal => exact fun w hw => hpost w (hhead.1 hw)
        | jump _ => exact hpost
        | special _ => exact hpost
        | cpuExn _ => exact hpost
      | ifElse c yes no =>
        rw [deadcode_stmtLive_ifElse] at ha ⊢
        rw [propagate_exec_ifElse] at h
        simp only
        rw [propagate_exec_ifElse]
        rw [← deadcode_sim_eval ha (fun w hw => (deadcode_mem_addVars _ _ w).mpr (Or.inl hw))]
        rcases propagate_bind_ok h with ⟨v, hv, h⟩
        rw [hv]
        simp only [propagate_ok_bind]
        simp only [propagate_branchStep] at h ⊢
        rcases propagate_bind_ok h with ⟨bits, hbits, h⟩
        rw [hbits]
        simp only [propagate_ok_bind] at h ⊢
        have hay : deadcode_Agree (program o live yes).1 st.env st'.env := fun w hw =>
          ha w ((deadcode_mem_addVars _ _ w).mpr (Or.inr (List.mem_append_left _ hw)))
        have han : deadcode_Agree (program o live no).1 st.env st'.env := fun w hw =>
          ha w ((deadcode_mem_addVars _ _ w).mpr (Or.inr (List.mem_append_right _ hw)))
        split at h
        · rename_i hw
          simp only [hw, ite_true]
          split at h
          · rename_i hcv
            simp only [hcv, ite_true]
            exact ihP yes live st st' next eff hay h
          · rename_i hcv
            simp only [hcv, ite_false]
            exact ihP no live st st' next eff han h
        · cases h
    refine ⟨stmtStep, loop, ?_⟩
    intro code live st st' next eff ha h
    cases code with
    | nil =>
      simp only [deadcode_program_nil] at ha ⊢
      simp only [propagate_exec_nil] at h ⊢
      cases h
      exact ⟨st', rfl, ha⟩
    | cons head tail =>
      rw [deadcode_program_cons] at ha ⊢
      rw [propagate_exec_cons] at h
      rcases propagate_bind_ok h with ⟨⟨n, e⟩, hr, h⟩
      have hsim := ihS head (program o live tail).1 st st' n e ha hr
      cases hs : (stmtLive o (program o live tail).1 head).2 with
      | none =>
        rw [hs] at hsim
        obtain ⟨hpost, he⟩ := hsim
        cases e with
        | normal =>
          obtain ⟨n', hn, hp⟩ := ihP tail live n st' next eff hpost h
          exact ⟨n', by simpa using (deadcode_exec_fuel_succ f).2 _ _ _ hn, hp⟩
        | jump _ => cases he
        | special _ => cases he
        | cpuExn _ => cases he
      | some t =>
        rw [hs] at hsim
        obtain ⟨n', hn, hpost⟩ := hsim
        simp only [Option.toList_some, List.singleton_append]
        rw [propagate_exec_cons, hn]
        simp only [propagate_ok_bind]
        cases e with
        | normal => exact ihP tail live n n' next eff hpost h
        | jump _ => cases h; exact ⟨n', rfl, hpost⟩
        | special _ => cases h; exact ⟨n', rfl, hpost⟩
        | cpuExn _ => cases h; exact ⟨n', rfl, hpost⟩

/-- Preservation for every program: if the original run succeeds, the optimized program succeeds
from the same state with the same fuel and exactly the same effect, and every output variable has
the same value, or is unbound in both.

This is one-directional by design. A deleted move is never evaluated, so if its evaluation would
have failed the optimized program can succeed where the original fails; see
`deadcode_deleted_move_may_hide_error`. Variables that are not outputs are unconstrained. -/
theorem deadcode_run_preserves (code : Bil.Program) (st next : State) (eff : Effect) (fuel : Nat)
    (h : run code st fuel = .ok (next, eff)) :
    ∃ next', run (optimize o code) st fuel = .ok (next', eff) ∧
      ∀ x ∈ o, lookup next.env x = lookup next'.env x := by
  obtain ⟨n', hn, hp⟩ := (deadcode_sim o fuel).2.2 code o st st next eff (fun _ _ => rfl) h
  refine ⟨n', hn, ?_⟩
  cases eff with
  | normal => exact hp
  | jump _ => exact hp
  | special _ => exact hp
  | cpuExn _ => exact hp

/-- Intended: deleting a dead move can hide its failure, as upstream `prune_dead_virtuals` deletes
without evaluating. Here the original fails on the unbound `u` and the optimized program succeeds,
which is why `deadcode_run_preserves` assumes the original succeeded. -/
theorem deadcode_deleted_move_may_hide_error (x u : Bap.Var) (hx : deadcode_isMem x.typ = false) :
    (run [.move x (.var u)] {} 10).toOption = none ∧
      optimize [] [.move x (.var u)] = [] ∧
      (run (optimize [] [.move x (.var u)]) {} 10).toOption.isSome = true := by
  have hopt : optimize [] [.move x (.var u)] = [] := by
    show (program [] [] [.move x (.var u)]).2 = []
    simp only [deadcode_program_cons, deadcode_program_nil]
    rw [deadcode_move_dead [] _ hx (by simp)]
    rfl
  refine ⟨?_, hopt, ?_⟩
  · simp only [run, propagate_exec_cons, propagate_exec_move, evalExp, lookup]
    rfl
  · rw [hopt]
    rfl

/-- Regression: a write before a jump survives when it is an output, whatever follows the jump. -/
theorem deadcode_keeps_write_before_jump (x : Bap.Var) (a t b : Exp) (hfree : freeVars t = []) :
    optimize [x] [.move x a, .jmp t, .move x b] = [.move x a, .jmp t, .move x b] := by
  show (program [x] [x] _).2 = _
  simp only [deadcode_program_cons, deadcode_program_nil, deadcode_stmtLive_jmp, hfree]
  cases hm : deadcode_isMem x.typ with
  | true => simp [deadcode_move_mem _ _ hm, deadcode_stmtLive_jmp, hfree]
  | false =>
    have hl : x ∈ addVars [x] [] := (deadcode_mem_addVars _ _ _).mpr (Or.inl (by simp))
    simp [deadcode_move_live _ _ hm, deadcode_stmtLive_jmp, hfree, hl]

/-- Everything an exit needs is live before a jump, a special or a CPU exception. -/
theorem deadcode_outputs_live_at_exit (l : List Bap.Var) (t : Exp) (m : String) (n : Nat) :
    o ⊆ (stmtLive o l (.jmp t)).1 ∧ o ⊆ (stmtLive o l (.special m)).1 ∧ o ⊆ (stmtLive o l (.cpuExn n)).1 := by
  rw [deadcode_stmtLive_jmp, deadcode_stmtLive_special, deadcode_stmtLive_cpuExn]
  exact ⟨fun v hv => (deadcode_mem_addVars _ _ v).mpr (Or.inl hv), fun _ h => h, fun _ h => h⟩

end DeadCode

section Taint

set_option linter.unusedSimpArgs false

section Evaluation

open Bap.Bil

/-- `b` reproduces every successful lookup of `a`. -/
def taint_Extends (a b : Env) : Prop :=
  ∀ v r, lookup a v = .ok r → lookup b v = .ok r

private theorem taint_env_find_filter (env : Env) (k w : Bap.Var) (h : w ≠ k) :
    (env.filter fun b => b.1 != k).find? (fun b => b.1 == w) = env.find? (fun b => b.1 == w) := by
  induction env with
  | nil => rfl
  | cons head tail ih =>
    by_cases hv : head.1 = k
    · have : head.1 ≠ w := fun e => h (e.symm.trans hv)
      simp [hv, List.filter_cons, List.find?_cons, h.symm, this] at ih ⊢
      exact ih
    · by_cases hw : head.1 = w
      · simp [hv, hw, List.filter_cons, List.find?_cons, h]
      · simp [hv, hw, List.filter_cons, List.find?_cons, ih] at ih ⊢

theorem taint_lookup_bind (env : Env) (v w : Bap.Var) (r : Value) :
    lookup (Bil.bind env v r) w = if w = v then .ok r else lookup env w := by
  by_cases h : w = v
  · subst h; simp [lookup, Bil.bind]
  · have hh : ¬ v = w := fun e => h e.symm
    unfold lookup Bil.bind
    rw [List.find?_cons]
    have e : ((v, r).1 == w) = false := by simpa using hh
    rw [e]
    simp only [h, ite_false]
    rw [taint_env_find_filter env v w h]

private theorem taint_Extends_bind {a b : Env} (h : taint_Extends a b) (v : Bap.Var) (r : Value) :
    taint_Extends (Bil.bind a v r) (Bil.bind b v r) := by
  intro w s hs
  rw [taint_lookup_bind] at hs ⊢
  split at hs
  · simp [*] at hs ⊢
  · simp only [*, ite_false]; exact h w s hs

private def taint_R {α} (x y : Except String α) : Prop := ∀ v, x = .ok v → y = .ok v

private theorem taint_R_refl {α} (x : Except String α) : taint_R x x := fun _ h => h

private theorem taint_R_bind {α β} {x y : Except String α} {f g : α → Except String β}
    (h : taint_R x y) (k : ∀ v, taint_R (f v) (g v)) : taint_R (x >>= f) (y >>= g) := by
  intro r hr
  cases hx : x with
  | error e => rw [hx] at hr; cases hr
  | ok v =>
    rw [hx] at hr
    rw [h v hx]
    exact k v r hr

private theorem taint_bind_ok {α β ε} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | error e => cases h

/-- Evaluation is stable under extending the environment. -/
theorem taint_eval_extends (e : Exp) : ∀ {a b : Env}, taint_Extends a b →
    ∀ r, evalExp a e = .ok r → evalExp b e = .ok r := by
  have main : ∀ {a b : Env}, taint_Extends a b → taint_R (evalExp a e) (evalExp b e) := by
    induction e with
    | int v => intro a b _; exact taint_R_refl _
    | var v => intro a b h; simp only [evalExp]; exact h v
    | load m ad _ _ im ia =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (im h) fun _ => taint_R_bind (taint_R_refl _) fun _ =>
        taint_R_bind (ia h) fun _ => taint_R_refl _
    | store m ad val _ _ im ia iv =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (im h) fun _ => taint_R_bind (taint_R_refl _) fun _ =>
        taint_R_bind (ia h) fun _ => taint_R_bind (taint_R_refl _) fun _ =>
        taint_R_bind (iv h) fun _ => taint_R_refl _
    | bin _ _ _ il ir =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (il h) fun _ => taint_R_bind (taint_R_refl _) fun _ =>
        taint_R_bind (ir h) fun _ => taint_R_refl _
    | un _ _ i =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (i h) fun _ => taint_R_refl _
    | cast _ _ _ i =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (i h) fun _ => taint_R_refl _
    | letIn v _ _ il ib =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (il h) fun r => ib (taint_Extends_bind h v r)
    | ite _ _ _ ic iy in_ =>
      intro a b h
      simp only [evalExp]
      refine taint_R_bind (ic h) fun _ => taint_R_bind (taint_R_refl _) ?_
      rintro ⟨w, cv⟩
      by_cases hw : w = 1
      · subst hw
        simp only [dite_true]
        split
        · exact iy h
        · exact in_ h
      · simpa [hw] using taint_R_refl _
    | extract _ _ _ i =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (i h) fun _ => taint_R_refl _
    | concat _ _ il ir =>
      intro a b h
      simp only [evalExp]
      exact taint_R_bind (il h) fun _ => taint_R_bind (taint_R_refl _) fun _ =>
        taint_R_bind (ir h) fun _ => taint_R_refl _
    | unknown _ _ => intro a b _; exact taint_R_refl _
  intro a b h r k
  exact main h r k

private theorem taint_Extends_nil (env : Env) : taint_Extends [] env := by
  intro v r h; simp [lookup] at h

/-- A closed expression (one that evaluates in the empty environment) evaluates to the same
value everywhere. -/
theorem taint_eval_closed {e : Exp} {r : Value} (env : Env) (h : evalExp [] e = .ok r) :
    evalExp env e = .ok r :=
  taint_eval_extends e (taint_Extends_nil env) r h
end Evaluation

open Bap.Analysis.Taint
open_private Bap.Analysis.Taint in Bap.Analysis.Taint :
  union putVar putMemory byteLabels constant bytes allLabels memoryLabels store joinBindings
  assigned saturate loopFuel loopState

theorem taint_mem_union (l : Nat) (a b : Labels) : l ∈ union a b ↔ l ∈ a ∨ l ∈ b := by
  simp [union, List.mem_eraseDups]

private theorem taint_find_filter {α β : Type} [DecidableEq α] (bs : List (α × β)) (k w : α) :
    (bs.filter fun b => b.1 != k).find? (fun b => b.1 = w) =
      if w = k then none else bs.find? fun b => b.1 = w := by
  induction bs with
  | nil => simp
  | cons head tail ih =>
    by_cases hk : head.1 = k <;> by_cases hw : head.1 = w
    · subst hk; subst hw; simp [List.filter_cons, ih]
    · subst hk
      have : w ≠ head.1 := fun h => hw h.symm
      simp [List.filter_cons, List.find?_cons, ih, hw, this]
    · subst hw; simp [List.filter_cons, List.find?_cons, hk]
    · simp [List.filter_cons, List.find?_cons, hk, hw, ih]

theorem taint_labelsOfVar_putVar (s : State) (v w : Bap.Var) (l : Labels) :
    labelsOfVar (putVar v l s) w = if w = v then l else labelsOfVar s w := by
  unfold labelsOfVar putVar
  cases l with
  | nil =>
    simp only [List.isEmpty_nil, ite_true]
    rw [taint_find_filter]
    by_cases hw : w = v <;> simp [hw]
  | cons h t =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.find?_cons]
    by_cases hw : v = w
    · subst hw; simp
    · have hw' : ¬ w = v := fun h => hw h.symm
      simp only [hw, hw', decide_false, ite_false]
      rw [taint_find_filter]
      simp [hw']

private theorem taint_byteLabels_putMemory (s : State) (a b : Nat) (l : Labels) :
    byteLabels (putMemory a l s) b = if b = a then l else byteLabels s b := by
  unfold byteLabels putMemory
  cases l with
  | nil =>
    simp only [List.isEmpty_nil, ite_true]
    rw [taint_find_filter]
    by_cases hw : b = a <;> simp [hw]
  | cons h t =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.find?_cons]
    by_cases hw : a = b
    · subst hw; simp
    · have hw' : ¬ b = a := fun h => hw h.symm
      simp only [hw, hw', decide_false, ite_false]
      rw [taint_find_filter]
      simp [hw']

/-- Memory labels are what is known at the byte plus what may be anywhere. -/
theorem taint_mem_labelsOfMemory (s : State) (m n : Nat) :
    n ∈ labelsOfMemory s m ↔ n ∈ byteLabels s m ∨ n ∈ s.anywhere := by
  simp [labelsOfMemory, taint_mem_union]

@[simp] private theorem taint_anywhere_putVar (s : State) (v : Bap.Var) (l : Labels) :
    (putVar v l s).anywhere = s.anywhere := rfl

@[simp] private theorem taint_anywhere_putMemory (s : State) (a : Nat) (l : Labels) :
    (putMemory a l s).anywhere = s.anywhere := rfl

@[simp] private theorem taint_byteLabels_putVar (s : State) (v : Bap.Var) (l : Labels) (a : Nat) :
    byteLabels (putVar v l s) a = byteLabels s a := rfl

@[simp] private theorem taint_labelsOfVar_putMemory (s : State) (v : Bap.Var) (l : Labels) (a : Nat) :
    labelsOfVar (putMemory a l s) v = labelsOfVar s v := rfl

@[simp] private theorem taint_labelsOfMemory_putVar (s : State) (v : Bap.Var) (l : Labels) (a : Nat) :
    labelsOfMemory (putVar v l s) a = labelsOfMemory s a := rfl

theorem taint_labelsOfMemory_putMemory (s : State) (a b : Nat) (l : Labels) :
    labelsOfMemory (putMemory a l s) b = if b = a then union l s.anywhere else labelsOfMemory s b := by
  by_cases h : b = a <;> simp [labelsOfMemory, taint_byteLabels_putMemory, h]

/-- `sourceVar` adds exactly the new labels to the variable and leaves everything else alone. -/
theorem taint_mem_labelsOfVar_sourceVar (s : State) (v w : Bap.Var) (l : Labels) (n : Nat) :
    n ∈ labelsOfVar (sourceVar s v l) w ↔
      n ∈ labelsOfVar s w ∨ (w = v ∧ n ∈ l) := by
  by_cases hw : w = v
  · subst hw; simp [sourceVar, taint_labelsOfVar_putVar, taint_mem_union]
  · simp [sourceVar, taint_labelsOfVar_putVar, hw]

theorem taint_mem_labelsOfMemory_sourceMemory (s : State) (a b : Nat) (l : Labels) (n : Nat) :
    n ∈ labelsOfMemory (sourceMemory s a l) b ↔
      n ∈ labelsOfMemory s b ∨ (b = a ∧ n ∈ l) := by
  simp only [taint_mem_labelsOfMemory, sourceMemory, taint_anywhere_putMemory,
    taint_byteLabels_putMemory]
  by_cases hw : b = a
  · subst hw
    simp [taint_mem_union, or_assoc, or_comm, or_left_comm]
  · simp [hw]

theorem taint_labelsOfMemory_sourceVar (s : State) (v : Bap.Var) (l : Labels) (a : Nat) :
    labelsOfMemory (sourceVar s v l) a = labelsOfMemory s a := rfl

theorem taint_labelsOfVar_sourceMemory (s : State) (v : Bap.Var) (l : Labels) (a : Nat) :
    labelsOfVar (sourceMemory s a l) v = labelsOfVar s v := rfl

theorem taint_labelsOfVar_clearVar (s : State) (v w : Bap.Var) :
    labelsOfVar (clearVar s v) w = if w = v then [] else labelsOfVar s w := by
  simp [clearVar, taint_labelsOfVar_putVar]

/-- Clearing a byte forgets what is known there. It is intended that labels a store with an
unresolved address may have left anywhere still apply to it. -/
theorem taint_labelsOfMemory_clearMemory (s : State) (a b : Nat) :
    labelsOfMemory (clearMemory s a) b =
      if b = a then s.anywhere.eraseDups else labelsOfMemory s b := by
  by_cases h : b = a <;> simp [clearMemory, labelsOfMemory, taint_byteLabels_putMemory, h, union]

theorem taint_clearVar_not_tainted (s : State) (v : Bap.Var) : v ∉ taintedVars (clearVar s v) := by
  simp [taintedVars, clearVar, putVar]

/-- A sourced variable with some label shows up in `taintedVars`, and nothing else is added. -/
theorem taint_mem_taintedVars_sourceVar (s : State) (v w : Bap.Var) (n : Nat) (l : Labels)
    (hn : n ∈ l) (hw : w ∈ taintedVars (sourceVar s v l)) : w = v ∨ w ∈ taintedVars s := by
  have : union (labelsOfVar s v) l ≠ [] := by
    intro h
    have := (taint_mem_union n (labelsOfVar s v) l).mpr (Or.inr hn)
    simp [h] at this
  simp only [taintedVars, sourceVar, putVar, List.mem_map] at hw ⊢
  rcases hw with ⟨b, hb, rfl⟩
  cases hu : union (labelsOfVar s v) l with
  | nil => exact absurd hu this
  | cons h t =>
    simp [hu] at hb
    rcases hb with hb | hb
    · simp [hb]
    · exact Or.inr ⟨b, hb.1, rfl⟩

/-- Pointwise inclusion of taint states. -/
def taint_Le (a b : State) : Prop :=
  (∀ v, labelsOfVar a v ⊆ labelsOfVar b v) ∧ (∀ m, labelsOfMemory a m ⊆ labelsOfMemory b m) ∧
    a.anywhere ⊆ b.anywhere

theorem taint_Le_refl (a : State) : taint_Le a a :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩

theorem taint_Le_trans {a b c : State} (h : taint_Le a b) (k : taint_Le b c) : taint_Le a c :=
  ⟨fun v _ m => k.1 v (h.1 v m), fun v _ m => k.2.1 v (h.2.1 v m), fun _ m => k.2.2 (h.2.2 m)⟩

private theorem taint_union_mono {a b c d : Labels} (h : a ⊆ c) (k : b ⊆ d) : union a b ⊆ union c d := by
  intro n hn
  rcases (taint_mem_union n _ _).mp hn with hn | hn
  · exact (taint_mem_union n _ _).mpr (Or.inl (h hn))
  · exact (taint_mem_union n _ _).mpr (Or.inr (k hn))

private theorem taint_union_le {a b c : Labels} (h : a ⊆ c) (k : b ⊆ c) : union a b ⊆ c := by
  intro n hn
  rcases (taint_mem_union n _ _).mp hn with hn | hn
  · exact h hn
  · exact k hn

private theorem taint_byteLabels_key {s : State} {k n : Nat} (h : n ∈ byteLabels s k) :
    k ∈ s.memory.map Prod.fst := by
  unfold byteLabels at h
  split at h
  · rename_i b hb
    have hk := List.find?_some hb
    have hm := List.mem_of_find?_eq_some hb
    simp only [decide_eq_true_eq] at hk
    exact List.mem_map.mpr ⟨b, hm, hk⟩
  · simp at h

/-- A load at an unresolved address sees every label any byte holds. -/
theorem taint_labelsOfMemory_subset_memoryLabels (s : State) (k : Nat) :
    labelsOfMemory s k ⊆ memoryLabels s := by
  intro n hn
  simp only [memoryLabels, taint_mem_union, List.mem_flatMap]
  rcases (taint_mem_labelsOfMemory s k n).mp hn with hn | hn
  · exact Or.inl ⟨k, taint_byteLabels_key hn, hn⟩
  · exact Or.inr hn

private theorem taint_memoryLabels_mono {a b : State} (h : taint_Le a b) : memoryLabels a ⊆ memoryLabels b := by
  intro n hn
  simp only [memoryLabels, taint_mem_union, List.mem_flatMap] at hn
  rcases hn with ⟨k, _, hn⟩ | hn
  · exact taint_labelsOfMemory_subset_memoryLabels b k
      (h.2.1 k ((taint_mem_labelsOfMemory a k n).mpr (Or.inl hn)))
  · simp only [memoryLabels, taint_mem_union]
    exact Or.inr (h.2.2 hn)

/-- Expression labels only grow when the state's labels grow. -/
theorem taint_exp_mono {a b : State} (h : taint_Le a b) (e : Bil.Exp) : exp a e ⊆ exp b e := by
  induction e with
  | int v => simp [exp]
  | var v => simpa [exp] using h.1 v
  | load m ad _ size im _ =>
    simp only [exp]
    refine taint_union_mono im ?_
    cases constant ad with
    | none => exact taint_memoryLabels_mono h
    | some address =>
      intro n hn
      simp only [List.mem_eraseDups, List.mem_flatMap] at hn ⊢
      rcases hn with ⟨k, hk, hn⟩
      exact ⟨k, hk, h.2.1 k hn⟩
  | store _ _ _ _ _ im ia iv =>
    simp only [exp]; exact taint_union_mono im (taint_union_mono ia iv)
  | bin _ _ _ il ir => simp only [exp]; exact taint_union_mono il ir
  | un _ _ i => simpa only [exp] using i
  | cast _ _ _ i => simpa only [exp] using i
  | letIn _ _ _ il ir => simp only [exp]; exact taint_union_mono il ir
  | ite _ _ _ _ iy in_ => simp only [exp]; exact taint_union_mono iy in_
  | extract _ _ _ i => simpa only [exp] using i
  | concat _ _ il ir => simp only [exp]; exact taint_union_mono il ir
  | unknown _ _ => simp [exp]

private theorem taint_Le_putVar {a b : State} (h : taint_Le a b) (v : Bap.Var) {l r : Labels}
    (k : l ⊆ r) : taint_Le (putVar v l a) (putVar v r b) := by
  refine ⟨fun w => ?_, fun m => by simpa using h.2.1 m, by simpa using h.2.2⟩
  simp only [taint_labelsOfVar_putVar]
  split
  · exact k
  · exact h.1 w

private theorem taint_Le_putVar_left {a b : State} (h : taint_Le a b) (v : Bap.Var) {l : Labels}
    (k : l ⊆ labelsOfVar b v) : taint_Le (putVar v l a) b := by
  refine ⟨fun w => ?_, fun m => by simpa using h.2.1 m, by simpa using h.2.2⟩
  simp only [taint_labelsOfVar_putVar]
  split
  · rename_i hw; subst hw; exact k
  · exact h.1 w

private theorem taint_Le_putMemory {a b : State} (h : taint_Le a b) (m : Nat) {l r : Labels}
    (k : l ⊆ r) : taint_Le (putMemory m l a) (putMemory m r b) := by
  refine ⟨fun w => by simpa using h.1 w, fun w => ?_, by simpa using h.2.2⟩
  simp only [taint_labelsOfMemory_putMemory]
  split
  · exact taint_union_mono k h.2.2
  · exact h.2.1 w

private theorem taint_Le_putMemory_left {a b : State} (h : taint_Le a b) (m : Nat) {l : Labels}
    (k : l ⊆ b.anywhere) : taint_Le (putMemory m l a) b := by
  refine ⟨fun w => by simpa using h.1 w, fun w => ?_, by simpa using h.2.2⟩
  simp only [taint_labelsOfMemory_putMemory]
  split
  · refine taint_union_le ?_ ?_
    · intro n hn; exact (taint_mem_labelsOfMemory b w n).mpr (Or.inr (k hn))
    · intro n hn; exact (taint_mem_labelsOfMemory b w n).mpr (Or.inr (h.2.2 hn))
  · exact h.2.1 w

/-- Writes `labels` over the bytes `bytes`, one by one. -/
private def taint_putAll (bytes : List Nat) (labels : Labels) (s : State) : State :=
  bytes.foldl (fun state byte => putMemory byte labels state) s

private theorem taint_Le_putAll {a b : State} (h : taint_Le a b) (bytes : List Nat) {l r : Labels}
    (k : l ⊆ r) : taint_Le (taint_putAll bytes l a) (taint_putAll bytes r b) := by
  induction bytes generalizing a b with
  | nil => exact h
  | cons head tail it => exact it (taint_Le_putMemory h head k)

private theorem taint_Le_putAll_left {a b : State} (h : taint_Le a b) (bytes : List Nat) {l : Labels}
    (k : l ⊆ b.anywhere) : taint_Le (taint_putAll bytes l a) b := by
  induction bytes generalizing a with
  | nil => exact h
  | cons head tail it => exact it (taint_Le_putMemory_left h head k)

private theorem taint_labelsOfMemory_putAll (bytes : List Nat) (l : Labels) (s : State) (m : Nat) :
    labelsOfMemory (taint_putAll bytes l s) m =
      if m ∈ bytes then union l s.anywhere else labelsOfMemory s m := by
  have hany : ∀ (bs : List Nat) (s : State), (taint_putAll bs l s).anywhere = s.anywhere := by
    intro bs
    induction bs with
    | nil => intro s; rfl
    | cons h t it => intro s; simp only [taint_putAll, List.foldl_cons]; exact (it _).trans rfl
  induction bytes generalizing s with
  | nil => simp [taint_putAll]
  | cons head tail it =>
    simp only [taint_putAll, List.foldl_cons]
    have := it (putMemory head l s)
    simp only [taint_putAll] at this
    rw [this]
    by_cases ht : m ∈ tail
    · simp [ht]
    · by_cases hh : m = head <;> simp [ht, hh, taint_labelsOfMemory_putMemory]

@[simp] private theorem taint_labelsOfVar_putAll (bytes : List Nat) (l : Labels) (s : State) (v : Bap.Var) :
    labelsOfVar (taint_putAll bytes l s) v = labelsOfVar s v := by
  induction bytes generalizing s with
  | nil => rfl
  | cons h t it => exact it _

private theorem taint_store_store (dst : Bap.Var) (s : State) (m ad val : Bil.Exp) (e : Endian) (z : Nat) :
    store dst s (.store m ad val e z) =
      match constant ad with
      | some address => taint_putAll (bytes address z) (union (exp s ad) (exp s val)) (store dst s m)
      | none =>
        { store dst s m with anywhere := union (store dst s m).anywhere (union (exp s ad) (exp s val)) } := by
  rw [store]
  rfl

private theorem taint_store_other (dst : Bap.Var) (s : State) (e : Bil.Exp)
    (hs : ∀ m ad val en z, e ≠ .store m ad val en z) (hv : ∀ v, e ≠ .var v) :
    store dst s e = putVar dst (exp s e) s := by
  cases e <;> first
    | exact absurd rfl (hs _ _ _ _ _)
    | exact absurd rfl (hv _)
    | simp [store]

private theorem taint_stmt_store (s : State) (v : Bap.Var) (m ad val : Bil.Exp) (e : Endian) (z : Nat) :
    stmt s (.move v (.store m ad val e z)) = store v s (.store m ad val e z) := by
  simp [stmt]

/-- A non-store move replaces the labels of its destination with those of its source. -/
theorem taint_stmt_move (s : State) (v : Bap.Var) (e : Bil.Exp)
    (he : ∀ m ad val en z, e ≠ .store m ad val en z) :
    stmt s (.move v e) = putVar v (exp s e) s := by
  cases e <;> first | (exact absurd rfl (he _ _ _ _ _)) | simp [stmt]

private theorem taint_stmt_while (s : State) (c : Bil.Exp) (body : List Bil.Stmt) :
    stmt s (.while c body) = loopState body (loopFuel s body) s := by
  simp [stmt]

private theorem taint_stmt_ifElse (s : State) (c : Bil.Exp) (y n : List Bil.Stmt) :
    stmt s (.ifElse c y n) = join (run s y) (run s n) := by
  simp [stmt]

private theorem taint_run_nil (s : State) : run s [] = s := by simp [run]

private theorem taint_run_cons (s : State) (h : Bil.Stmt) (t : List Bil.Stmt) :
    run s (h :: t) = run (stmt s h) t := by
  simp [run]

private theorem taint_loopState_zero (body : List Bil.Stmt) (s : State) :
    loopState body 0 s = saturate s body := by
  simp [loopState]

private theorem taint_loopState_succ (body : List Bil.Stmt) (f : Nat) (s : State) :
    loopState body (f + 1) s =
      if subsumed (join s (run s body)) s then s else loopState body f (join s (run s body)) := by
  rw [loopState]

/-! ### Joins -/

private def taint_look {α : Type} [DecidableEq α] (bs : List (α × Labels)) (k : α) : Labels :=
  match bs.find? fun b => b.1 = k with
  | some b => b.2
  | none => []

private theorem taint_look_nil_of_not_key {α : Type} [DecidableEq α] {bs : List (α × Labels)} {k : α}
    (h : k ∉ bs.map Prod.fst) : taint_look bs k = [] := by
  induction bs with
  | nil => rfl
  | cons b t it =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hb : b.1 ≠ k := fun e => h.1 e.symm
    have := it h.2
    simpa [taint_look, List.find?_cons, hb] using this

private theorem taint_look_filter {α : Type} [DecidableEq α] (bs : List (α × Labels)) (k : α)
    (p : α × Labels → Bool) (h : ∀ b, b.1 = k → p b = true) :
    taint_look (bs.filter p) k = taint_look bs k := by
  induction bs with
  | nil => rfl
  | cons b t it =>
    by_cases hk : b.1 = k
    · simp [taint_look, List.filter_cons, h b hk, hk]
    · by_cases hp : p b = true
      · simpa [taint_look, List.filter_cons, hp, hk, List.find?_cons] using it
      · simpa [taint_look, List.filter_cons, hp, hk, List.find?_cons] using it

private theorem taint_mem_look_map {α : Type} [DecidableEq α] (l R : List (α × Labels)) (F : α → Labels)
    (k : α) (n : Nat) :
    n ∈ taint_look (l.map (fun b => (b.1, union b.2 (F b.1))) ++ R) k ↔
      (k ∈ l.map Prod.fst ∧ (n ∈ taint_look l k ∨ n ∈ F k)) ∨
        (k ∉ l.map Prod.fst ∧ n ∈ taint_look R k) := by
  induction l with
  | nil => simp
  | cons b t it =>
    by_cases hk : b.1 = k
    · subst hk
      simp [taint_look, taint_mem_union]
    · have hk' : k ≠ b.1 := fun e => hk e.symm
      have e1 : taint_look (b :: t) k = taint_look t k := by simp [taint_look, hk]
      have e2 : taint_look (((b :: t).map fun b => (b.1, union b.2 (F b.1))) ++ R) k =
          taint_look ((t.map fun b => (b.1, union b.2 (F b.1))) ++ R) k := by
        simp [taint_look, hk]
      rw [e1, e2, it]
      simp [hk']

private theorem taint_mem_look_join {α : Type} [DecidableEq α] (l r : List (α × Labels)) (k : α) (n : Nat) :
    n ∈ taint_look (joinBindings l r) k ↔ n ∈ taint_look l k ∨ n ∈ taint_look r k := by
  refine Iff.trans (taint_mem_look_map l
    (r.filter fun binding => !l.any fun other => other.fst == binding.fst) (taint_look r) k n) ?_
  by_cases hk : k ∈ l.map Prod.fst
  · simp [hk]
  · rw [taint_look_filter r k _ ?_, taint_look_nil_of_not_key hk]
    · simp [hk]
    · intro b hb
      subst hb
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx e
      exact hk (List.mem_map.mpr ⟨x, hx, e⟩)

private theorem taint_labelsOfVar_eq_look (s : State) (v : Bap.Var) :
    labelsOfVar s v = taint_look s.vars v := by
  unfold labelsOfVar taint_look
  generalize List.find? _ s.vars = r
  cases r <;> rfl

private theorem taint_byteLabels_eq_look (s : State) (m : Nat) :
    byteLabels s m = taint_look s.memory m := by
  unfold byteLabels taint_look
  generalize List.find? _ s.memory = r
  cases r <;> rfl

theorem taint_mem_labelsOfVar_join (a b : State) (v : Bap.Var) (n : Nat) :
    n ∈ labelsOfVar (join a b) v ↔ n ∈ labelsOfVar a v ∨ n ∈ labelsOfVar b v := by
  simp only [taint_labelsOfVar_eq_look]
  exact taint_mem_look_join a.vars b.vars v n

private theorem taint_mem_byteLabels_join (a b : State) (m n : Nat) :
    n ∈ byteLabels (join a b) m ↔ n ∈ byteLabels a m ∨ n ∈ byteLabels b m := by
  simp only [taint_byteLabels_eq_look]
  exact taint_mem_look_join a.memory b.memory m n

theorem taint_mem_labelsOfMemory_join (a b : State) (m n : Nat) :
    n ∈ labelsOfMemory (join a b) m ↔ n ∈ labelsOfMemory a m ∨ n ∈ labelsOfMemory b m := by
  simp only [taint_mem_labelsOfMemory, taint_mem_byteLabels_join]
  simp only [join, taint_mem_union, or_assoc, or_comm, or_left_comm]

theorem taint_Le_join_left (a b : State) : taint_Le a (join a b) :=
  ⟨fun v _ h => (taint_mem_labelsOfVar_join a b v _).mpr (Or.inl h),
    fun m _ h => (taint_mem_labelsOfMemory_join a b m _).mpr (Or.inl h),
    fun _ h => by simp only [join, taint_mem_union]; exact Or.inl h⟩

theorem taint_Le_join_right (a b : State) : taint_Le b (join a b) :=
  ⟨fun v _ h => (taint_mem_labelsOfVar_join a b v _).mpr (Or.inr h),
    fun m _ h => (taint_mem_labelsOfMemory_join a b m _).mpr (Or.inr h),
    fun _ h => by simp only [join, taint_mem_union]; exact Or.inr h⟩

theorem taint_join_le {a b c : State} (h : taint_Le a c) (k : taint_Le b c) : taint_Le (join a b) c := by
  refine ⟨fun v n hn => ?_, fun m n hn => ?_, fun n hn => ?_⟩
  · rcases (taint_mem_labelsOfVar_join a b v n).mp hn with hn | hn
    · exact h.1 v hn
    · exact k.1 v hn
  · rcases (taint_mem_labelsOfMemory_join a b m n).mp hn with hn | hn
    · exact h.2.1 m hn
    · exact k.2.1 m hn
  · simp only [join, taint_mem_union] at hn
    rcases hn with hn | hn
    · exact h.2.2 hn
    · exact k.2.2 hn

private theorem taint_byteLabels_binding {s : State} {m n : Nat} (h : n ∈ byteLabels s m) :
    ∃ x ∈ s.memory, x.1 = m ∧ n ∈ x.2 := by
  unfold byteLabels at h
  split at h
  · rename_i x hx
    have hk := List.find?_some hx
    simp only [decide_eq_true_eq] at hk
    exact ⟨x, List.mem_of_find?_eq_some hx, hk, h⟩
  · simp at h

/-- `subsumed` is a sound check of `taint_Le`. It can answer false on a state with shadowed bindings
that `taint_Le` would accept, which costs a loop round and not soundness. -/
theorem taint_subsumed_sound {a b : State} (h : subsumed a b = true) : taint_Le a b := by
  simp only [subsumed, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨hv, hm⟩, ha⟩ := h
  have hany : a.anywhere ⊆ b.anywhere := fun n hn => ha n hn
  refine ⟨fun v n hn => ?_, fun m n hn => ?_, hany⟩
  · unfold labelsOfVar at hn
    split at hn
    · rename_i x hx
      have hk := List.find?_some hx
      simp only [decide_eq_true_eq] at hk
      subst hk
      exact hv x (List.mem_of_find?_eq_some hx) n hn
    · simp at hn
  · rcases (taint_mem_labelsOfMemory a m n).mp hn with hn | hn
    · obtain ⟨x, hx, hk, hl⟩ := taint_byteLabels_binding hn
      subst hk
      exact hm x hx n hl
    · exact (taint_mem_labelsOfMemory b m n).mpr (Or.inr (hany hn))

/-! ### Provenance -/

/-- All labels a state mentions. -/
def taint_labels (s : State) : Labels :=
  s.vars.flatMap Prod.snd ++ s.memory.flatMap Prod.snd ++ s.anywhere

private theorem taint_mem_labels (s : State) (n : Nat) :
    n ∈ taint_labels s ↔ (∃ b ∈ s.vars, n ∈ b.2) ∨ (∃ b ∈ s.memory, n ∈ b.2) ∨ n ∈ s.anywhere := by
  simp [taint_labels, List.mem_flatMap, or_assoc]

private theorem taint_labelsOfVar_subset (s : State) (v : Bap.Var) : labelsOfVar s v ⊆ taint_labels s := by
  intro n hn
  unfold labelsOfVar at hn
  split at hn
  · rename_i b hb
    exact (taint_mem_labels s n).mpr (Or.inl ⟨b, List.mem_of_find?_eq_some hb, hn⟩)
  · simp at hn

private theorem taint_byteLabels_subset (s : State) (m : Nat) : byteLabels s m ⊆ taint_labels s := by
  intro n hn
  obtain ⟨x, hx, _, hl⟩ := taint_byteLabels_binding hn
  exact (taint_mem_labels s n).mpr (Or.inr (Or.inl ⟨x, hx, hl⟩))

private theorem taint_anywhere_subset (s : State) : s.anywhere ⊆ taint_labels s := fun n hn =>
  (taint_mem_labels s n).mpr (Or.inr (Or.inr hn))

private theorem taint_labelsOfMemory_subset (s : State) (m : Nat) : labelsOfMemory s m ⊆ taint_labels s := by
  intro n hn
  rcases (taint_mem_labelsOfMemory s m n).mp hn with hn | hn
  · exact taint_byteLabels_subset s m hn
  · exact taint_anywhere_subset s hn

private theorem taint_memoryLabels_subset (s : State) : memoryLabels s ⊆ taint_labels s := by
  intro n hn
  simp only [memoryLabels, taint_mem_union, List.mem_flatMap] at hn
  rcases hn with ⟨k, _, hn⟩ | hn
  · exact taint_byteLabels_subset s k hn
  · exact taint_anywhere_subset s hn

theorem taint_exp_provenance (s : State) (e : Bil.Exp) : exp s e ⊆ taint_labels s := by
  induction e with
  | int v => simp [exp]
  | var v => simpa [exp] using taint_labelsOfVar_subset s v
  | load _ ad _ _ im _ =>
    simp only [exp]
    refine taint_union_le im ?_
    cases constant ad with
    | none => exact taint_memoryLabels_subset s
    | some address =>
      intro n hn
      simp only [List.mem_eraseDups, List.mem_flatMap] at hn
      rcases hn with ⟨k, _, hn⟩
      exact taint_labelsOfMemory_subset s k hn
  | store _ _ _ _ _ im ia iv =>
    simp only [exp]; exact taint_union_le im (taint_union_le ia iv)
  | bin _ _ _ il ir | letIn _ _ _ il ir | concat _ _ il ir =>
    simp only [exp]; exact taint_union_le il ir
  | un _ _ i | cast _ _ _ i | extract _ _ _ i => simpa only [exp] using i
  | ite _ _ _ _ iy in_ => simp only [exp]; exact taint_union_le iy in_
  | unknown _ _ => simp [exp]

private theorem taint_labels_putVar (s : State) (v : Bap.Var) (l : Labels) (L : Labels)
    (hs : taint_labels s ⊆ L) (hl : l ⊆ L) : taint_labels (putVar v l s) ⊆ L := by
  intro n hn
  rcases (taint_mem_labels _ n).mp hn with ⟨b, hb, hn⟩ | hn | hn
  · simp only [putVar] at hb
    split at hb
    · exact hs ((taint_mem_labels s n).mpr (Or.inl ⟨b, (List.mem_filter.mp hb).1, hn⟩))
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hl hn
      · exact hs ((taint_mem_labels s n).mpr (Or.inl ⟨b, (List.mem_filter.mp hb).1, hn⟩))
  · exact hs ((taint_mem_labels s n).mpr (Or.inr (Or.inl hn)))
  · exact hs ((taint_mem_labels s n).mpr (Or.inr (Or.inr hn)))

private theorem taint_labels_putMemory (s : State) (a : Nat) (l : Labels) (L : Labels)
    (hs : taint_labels s ⊆ L) (hl : l ⊆ L) : taint_labels (putMemory a l s) ⊆ L := by
  intro n hn
  rcases (taint_mem_labels _ n).mp hn with hn | ⟨b, hb, hn⟩ | hn
  · exact hs ((taint_mem_labels s n).mpr (Or.inl hn))
  · simp only [putMemory] at hb
    split at hb
    · exact hs ((taint_mem_labels s n).mpr (Or.inr (Or.inl ⟨b, (List.mem_filter.mp hb).1, hn⟩)))
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hl hn
      · exact hs ((taint_mem_labels s n).mpr (Or.inr (Or.inl ⟨b, (List.mem_filter.mp hb).1, hn⟩)))
  · exact hs ((taint_mem_labels s n).mpr (Or.inr (Or.inr hn)))

private theorem taint_labels_putAll (bytes : List Nat) (s : State) (l L : Labels)
    (hs : taint_labels s ⊆ L) (hl : l ⊆ L) : taint_labels (taint_putAll bytes l s) ⊆ L := by
  induction bytes generalizing s with
  | nil => exact hs
  | cons h t it => exact it _ (taint_labels_putMemory s h l L hs hl)

private theorem taint_mem_joinBindings_flat {α : Type} [DecidableEq α] (l r : List (α × Labels)) (n : Nat)
    (h : ∃ b ∈ joinBindings l r, n ∈ b.2) : (∃ b ∈ l, n ∈ b.2) ∨ ∃ b ∈ r, n ∈ b.2 := by
  rcases h with ⟨b, hb, hn⟩
  unfold joinBindings at hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    rcases (taint_mem_union n _ _).mp hn with hn | hn
    · exact Or.inl ⟨c, hc, hn⟩
    · simp only at hn
      split at hn
      · rename_i x hx
        exact Or.inr ⟨x, List.mem_of_find?_eq_some hx, hn⟩
      · simp at hn
  · exact Or.inr ⟨b, (List.mem_filter.mp hb).1, hn⟩

private theorem taint_labels_join (a b : State) (L : Labels) (ha : taint_labels a ⊆ L)
    (hb : taint_labels b ⊆ L) : taint_labels (join a b) ⊆ L := by
  intro n hn
  rcases (taint_mem_labels _ n).mp hn with hn | hn | hn
  · rcases taint_mem_joinBindings_flat _ _ n hn with hn | hn
    · exact ha ((taint_mem_labels a n).mpr (Or.inl hn))
    · exact hb ((taint_mem_labels b n).mpr (Or.inl hn))
  · rcases taint_mem_joinBindings_flat _ _ n hn with hn | hn
    · exact ha ((taint_mem_labels a n).mpr (Or.inr (Or.inl hn)))
    · exact hb ((taint_mem_labels b n).mpr (Or.inr (Or.inl hn)))
  · simp only [join, taint_mem_union] at hn
    rcases hn with hn | hn
    · exact ha (taint_anywhere_subset a hn)
    · exact hb (taint_anywhere_subset b hn)

private theorem taint_labels_store (dst : Bap.Var) (s : State) (e : Bil.Exp) (L : Labels)
    (hs : taint_labels s ⊆ L) : taint_labels (store dst s e) ⊆ L := by
  have hexp : ∀ e, exp s e ⊆ L := fun e _ h => hs (taint_exp_provenance s e h)
  induction e with
  | store m ad val en z im _ _ =>
    rw [taint_store_store]
    have hl : union (exp s ad) (exp s val) ⊆ L := taint_union_le (hexp _) (hexp _)
    cases constant ad with
    | some address => exact taint_labels_putAll _ _ _ _ im hl
    | none =>
      intro n hn
      rcases (taint_mem_labels _ n).mp hn with hn | hn | hn
      · exact im ((taint_mem_labels _ n).mpr (Or.inl hn))
      · exact im ((taint_mem_labels _ n).mpr (Or.inr (Or.inl hn)))
      · simp only [taint_mem_union] at hn
        rcases hn with hn | hn | hn
        · exact im (taint_anywhere_subset _ hn)
        · exact hexp _ hn
        · exact hexp _ hn
  | var source =>
    simp only [store]
    split
    · exact hs
    · exact taint_labels_putVar _ _ _ _ hs fun _ h => hs (taint_labelsOfVar_subset s source h)
  | _ => simp only [store]; exact taint_labels_putVar _ _ _ _ hs (hexp _)

private theorem taint_mem_allLabels (s : State) (n : Nat) : n ∈ allLabels s ↔ n ∈ taint_labels s := by
  simp [allLabels, taint_labels, List.mem_eraseDups]

/-- What `saturate` does to variables, given the assigned list. -/
private def taint_satVars (labels : Labels) (vars : List Bap.Var) (s : State) : State :=
  vars.foldl (fun state var => putVar var (union (labelsOfVar state var) labels) state) s

private theorem taint_saturate_eq (s : State) (body : List Bil.Stmt) :
    saturate s body =
      { taint_satVars (allLabels s) (body.flatMap assigned) s with anywhere := allLabels s } := rfl

private theorem taint_satVars_var (labels : Labels) (vars : List Bap.Var) (s : State) (w : Bap.Var) (n : Nat) :
    n ∈ labelsOfVar (taint_satVars labels vars s) w ↔
      n ∈ labelsOfVar s w ∨ (w ∈ vars ∧ n ∈ labels) := by
  induction vars generalizing s with
  | nil => simp [taint_satVars]
  | cons h t it =>
    simp only [taint_satVars, List.foldl_cons]
    have := it (putVar h (union (labelsOfVar s h) labels) s)
    simp only [taint_satVars] at this
    rw [this, taint_labelsOfVar_putVar]
    by_cases hw : w = h
    · subst hw
      by_cases hl : n ∈ labels <;> simp [taint_mem_union, or_assoc, hl]
    · simp [hw]

@[simp] private theorem taint_satVars_memory (labels : Labels) (vars : List Bap.Var) (s : State) :
    (taint_satVars labels vars s).memory = s.memory := by
  induction vars generalizing s with
  | nil => rfl
  | cons h t it => exact it _

@[simp] private theorem taint_satVars_anywhere (labels : Labels) (vars : List Bap.Var) (s : State) :
    (taint_satVars labels vars s).anywhere = s.anywhere := by
  induction vars generalizing s with
  | nil => rfl
  | cons h t it => exact it _

private theorem taint_labels_satVars (labels : Labels) (vars : List Bap.Var) (s : State) (L : Labels)
    (hs : taint_labels s ⊆ L) (hl : labels ⊆ L) : taint_labels (taint_satVars labels vars s) ⊆ L := by
  induction vars generalizing s with
  | nil => exact hs
  | cons h t it =>
    exact it _ (taint_labels_putVar _ _ _ _ hs (taint_union_le
      (fun _ k => hs (taint_labelsOfVar_subset s h k)) hl))

private theorem taint_labels_saturate (s : State) (body : List Bil.Stmt) :
    taint_labels (saturate s body) ⊆ taint_labels s := by
  rw [taint_saturate_eq]
  have hall : allLabels s ⊆ taint_labels s := fun n h => (taint_mem_allLabels s n).mp h
  have hsat := taint_labels_satVars (allLabels s) (body.flatMap assigned) s (taint_labels s)
    (fun _ h => h) hall
  intro n hn
  rcases (taint_mem_labels _ n).mp hn with hn | hn | hn
  · exact hsat ((taint_mem_labels _ n).mpr (Or.inl hn))
  · exact hsat ((taint_mem_labels _ n).mpr (Or.inr (Or.inl hn)))
  · exact hall hn

private theorem taint_foldl_provenance {code : List Bil.Stmt}
    (ih : ∀ s ∈ code, ∀ a L, taint_labels a ⊆ L → taint_labels (stmt a s) ⊆ L) :
    ∀ a L, taint_labels a ⊆ L → taint_labels (run a code) ⊆ L := by
  induction code with
  | nil => intro a L h; rwa [taint_run_nil]
  | cons head tail it =>
    intro a L h
    rw [taint_run_cons]
    exact it (fun s hs => ih s (List.mem_cons_of_mem _ hs)) _ _ (ih head (by simp) a L h)

/-- Statements never invent labels. -/
theorem taint_stmt_provenance (s : Bil.Stmt) : ∀ a L, taint_labels a ⊆ L → taint_labels (stmt a s) ⊆ L := by
  induction s using stmtInduction with
  | move v e =>
    intro a L h
    by_cases he : ∀ m ad val en z, e ≠ .store m ad val en z
    · rw [taint_stmt_move _ _ _ he]
      exact taint_labels_putVar _ _ _ _ h fun _ k => h (taint_exp_provenance a e k)
    · simp only [ne_eq, Classical.not_forall, Classical.not_not] at he
      rcases he with ⟨m, ad, val, en, z, rfl⟩
      rw [taint_stmt_store]
      exact taint_labels_store _ _ _ _ h
  | jmp _ => intro a L h; simpa [stmt] using h
  | special _ => intro a L h; simpa [stmt] using h
  | cpuExn _ => intro a L h; simpa [stmt] using h
  | while_ c body ih =>
    intro a L h
    rw [taint_stmt_while]
    generalize loopFuel a body = f
    induction f generalizing a with
    | zero =>
      rw [taint_loopState_zero]
      exact fun _ k => h (taint_labels_saturate a body k)
    | succ f it =>
      rw [taint_loopState_succ]
      split
      · exact h
      · exact it _ (taint_labels_join _ _ _ h (taint_foldl_provenance ih a L h))
  | ifElse c y n iy in_ =>
    intro a L h
    rw [taint_stmt_ifElse]
    exact taint_labels_join _ _ _ (taint_foldl_provenance iy a L h) (taint_foldl_provenance in_ a L h)

/-- Provenance: every label after a run was already present in the initial state. -/
theorem taint_run_provenance (a : State) (code : Bil.Program) :
    taint_labels (run a code) ⊆ taint_labels a :=
  taint_foldl_provenance (fun s _ => taint_stmt_provenance s) a _ fun _ h => h

private theorem taint_run_provenance_le (a : State) (code : Bil.Program) (L : Labels)
    (h : taint_labels a ⊆ L) : taint_labels (run a code) ⊆ L :=
  taint_foldl_provenance (fun s _ => taint_stmt_provenance s) a L h

/-! ### Loop fixpoints -/

private theorem taint_assigned_while (c : Bil.Exp) (b : List Bil.Stmt) :
    assigned (.while c b) = b.flatMap assigned := by simp [assigned]

private theorem taint_assigned_ifElse (c : Bil.Exp) (y n : List Bil.Stmt) :
    assigned (.ifElse c y n) = y.flatMap assigned ++ n.flatMap assigned := by simp [assigned]

private theorem taint_Le_le_saturate (s : State) (body : List Bil.Stmt) : taint_Le s (saturate s body) := by
  rw [taint_saturate_eq]
  have hall : s.anywhere ⊆ allLabels s := fun n h =>
    (taint_mem_allLabels s n).mpr (taint_anywhere_subset s h)
  refine ⟨fun v n hn => ?_, fun m n hn => ?_, hall⟩
  · exact (taint_satVars_var _ _ s v n).mpr (Or.inl hn)
  · rcases (taint_mem_labelsOfMemory s m n).mp hn with hn | hn
    · refine (taint_mem_labelsOfMemory _ m n).mpr (Or.inl ?_)
      simpa [byteLabels] using hn
    · exact (taint_mem_labelsOfMemory _ m n).mpr (Or.inr (hall hn))

/-- `U` absorbs `L` in memory and in `vars`: no statement assigning only `vars` can leave it. -/
private structure TaintBound (U : State) (L : Labels) (vars : List Bap.Var) : Prop where
  anywhere : L ⊆ U.anywhere
  var : ∀ v ∈ vars, L ⊆ labelsOfVar U v

private theorem taint_store_bound {U : State} {L : Labels} {vars : List Bap.Var} (hU : TaintBound U L vars)
    {dst : Bap.Var} (hd : dst ∈ vars) {X : State} (hX : taint_Le X U) (hL : taint_labels X ⊆ L) (e : Bil.Exp) :
    taint_Le (store dst X e) U := by
  have hexp : ∀ e, exp X e ⊆ L := fun e _ h => hL (taint_exp_provenance X e h)
  induction e with
  | store m ad val en z im _ _ =>
    rw [taint_store_store]
    have hl : union (exp X ad) (exp X val) ⊆ L := taint_union_le (hexp _) (hexp _)
    cases constant ad with
    | some address => exact taint_Le_putAll_left im _ fun _ h => hU.anywhere (hl h)
    | none =>
      refine ⟨im.1, fun w n hn => ?_, fun n hn => ?_⟩
      · rcases (taint_mem_labelsOfMemory _ w n).mp hn with hn | hn
        · exact im.2.1 w ((taint_mem_labelsOfMemory _ w n).mpr (Or.inl hn))
        · simp only [taint_mem_union] at hn
          rcases hn with hn | hn
          · exact im.2.1 w ((taint_mem_labelsOfMemory _ w n).mpr (Or.inr hn))
          · exact (taint_mem_labelsOfMemory U w n).mpr (Or.inr (hU.anywhere (hl ((taint_mem_union _ _ _).mpr hn))))
      · simp only [taint_mem_union] at hn
        rcases hn with hn | hn
        · exact im.2.2 hn
        · exact hU.anywhere (hl ((taint_mem_union _ _ _).mpr hn))
  | var source =>
    simp only [store]
    split
    · exact hX
    · exact taint_Le_putVar_left hX _ fun _ h => hU.var dst hd (hL (taint_labelsOfVar_subset X source h))
  | _ =>
    simp only [store]
    exact taint_Le_putVar_left hX _ fun _ h => hU.var dst hd (hexp _ h)

private theorem taint_stmt_bound {U : State} {L : Labels} (s : Bil.Stmt) :
    ∀ {vars : List Bap.Var}, TaintBound U L vars → (∀ v ∈ assigned s, v ∈ vars) →
    ∀ X, taint_Le X U → taint_labels X ⊆ L → taint_Le (stmt X s) U := by
  have runBound : ∀ {code : List Bil.Stmt} {vars : List Bap.Var},
      (∀ s ∈ code, TaintBound U L vars → (∀ v ∈ assigned s, v ∈ vars) →
        ∀ X, taint_Le X U → taint_labels X ⊆ L → taint_Le (stmt X s) U) →
      TaintBound U L vars → (∀ v ∈ code.flatMap assigned, v ∈ vars) →
      ∀ X, taint_Le X U → taint_labels X ⊆ L → taint_Le (run X code) U := by
    intro code vars ih hU ha
    induction code with
    | nil => intro X h _; rwa [taint_run_nil]
    | cons head tail it =>
      intro X h hL
      rw [taint_run_cons]
      simp only [List.flatMap_cons, List.mem_append] at ha
      exact it (fun s hs => ih s (List.mem_cons_of_mem _ hs)) (fun v hv => ha v (Or.inr hv)) _
        (ih head (by simp) hU (fun v hv => ha v (Or.inl hv)) X h hL)
        (taint_stmt_provenance head X L hL)
  induction s using stmtInduction with
  | move v e =>
    intro vars hU ha X hX hL
    have hd : v ∈ vars := ha v (by simp [assigned])
    by_cases he : ∀ m ad val en z, e ≠ .store m ad val en z
    · rw [taint_stmt_move _ _ _ he]
      exact taint_Le_putVar_left hX _ fun _ h => hU.var v hd (hL (taint_exp_provenance X e h))
    · simp only [ne_eq, Classical.not_forall, Classical.not_not] at he
      rcases he with ⟨m, ad, val, en, z, rfl⟩
      rw [taint_stmt_store]
      exact taint_store_bound hU hd hX hL _
  | jmp _ => intro _ _ _ X hX _; simpa [stmt] using hX
  | special _ => intro _ _ _ X hX _; simpa [stmt] using hX
  | cpuExn _ => intro _ _ _ X hX _; simpa [stmt] using hX
  | while_ c body ih =>
    intro vars hU ha X hX hL
    rw [taint_assigned_while] at ha
    rw [taint_stmt_while]
    generalize loopFuel X body = f
    induction f generalizing X with
    | zero =>
      rw [taint_loopState_zero, taint_saturate_eq]
      have hall : allLabels X ⊆ L := fun n h => hL ((taint_mem_allLabels X n).mp h)
      refine ⟨fun w n hn => ?_, fun m n hn => ?_, fun n hn => hU.anywhere (hall hn)⟩
      · rcases (taint_satVars_var _ _ X w n).mp hn with hn | ⟨hw, hn⟩
        · exact hX.1 w hn
        · exact hU.var w (ha w hw) (hall hn)
      · rcases (taint_mem_labelsOfMemory _ m n).mp hn with hn | hn
        · refine hX.2.1 m ((taint_mem_labelsOfMemory X m n).mpr (Or.inl ?_))
          simpa [byteLabels] using hn
        · exact (taint_mem_labelsOfMemory U m n).mpr (Or.inr (hU.anywhere (hall hn)))
    | succ f it =>
      rw [taint_loopState_succ]
      split
      · exact hX
      · refine it _ (taint_join_le hX (runBound (fun s hs => ih s hs) hU ha X hX hL))
          (taint_labels_join _ _ _ hL (taint_run_provenance_le X body L hL))
  | ifElse c y n iy in_ =>
    intro vars hU ha X hX hL
    rw [taint_assigned_ifElse] at ha
    simp only [List.mem_append] at ha
    rw [taint_stmt_ifElse]
    exact taint_join_le (runBound (fun s hs => iy s hs) hU (fun v h => ha v (Or.inl h)) X hX hL)
      (runBound (fun s hs => in_ s hs) hU (fun v h => ha v (Or.inr h)) X hX hL)

private theorem taint_run_bound {U : State} {L : Labels} {vars : List Bap.Var} (hU : TaintBound U L vars)
    (code : List Bil.Stmt) (ha : ∀ v ∈ code.flatMap assigned, v ∈ vars) :
    ∀ X, taint_Le X U → taint_labels X ⊆ L → taint_Le (run X code) U := by
  induction code with
  | nil => intro X h _; rwa [taint_run_nil]
  | cons head tail it =>
    intro X h hL
    rw [taint_run_cons]
    simp only [List.flatMap_cons, List.mem_append] at ha
    exact it (fun v hv => ha v (Or.inr hv)) _
      (taint_stmt_bound head hU (fun v hv => ha v (Or.inl hv)) X h hL)
      (taint_stmt_provenance head X L hL)

/-- `saturate` really is stable: one more run of the loop body adds nothing to it. -/
theorem taint_saturate_stable (s : State) (body : List Bil.Stmt) :
    taint_Le (run (saturate s body) body) (saturate s body) := by
  have hall : ∀ n, n ∈ allLabels s ↔ n ∈ taint_labels s := taint_mem_allLabels s
  have hU : TaintBound (saturate s body) (allLabels s) (body.flatMap assigned) := by
    refine ⟨fun n hn => ?_, fun v hv n hn => ?_⟩
    · rw [taint_saturate_eq]; exact hn
    · rw [taint_saturate_eq]
      exact (taint_satVars_var _ _ s v n).mpr (Or.inr ⟨hv, hn⟩)
  exact taint_run_bound hU body (fun _ h => h) _ (taint_Le_refl _)
    fun n h => (hall n).mpr (taint_labels_saturate s body h)

/-- The result of the loop iteration is above its start and is stable under the loop body,
whether iteration converges or fuel runs out. -/
theorem taint_loopState_postfix (body : List Bil.Stmt) (f : Nat) (s : State) :
    taint_Le s (loopState body f s) ∧
      taint_Le (run (loopState body f s) body) (loopState body f s) := by
  induction f generalizing s with
  | zero =>
    rw [taint_loopState_zero]
    exact ⟨taint_Le_le_saturate s body, taint_saturate_stable s body⟩
  | succ f it =>
    rw [taint_loopState_succ]
    split
    · rename_i hsub
      exact ⟨taint_Le_refl s, taint_Le_trans (taint_Le_join_right s _) (taint_subsumed_sound hsub)⟩
    · obtain ⟨h1, h2⟩ := it (join s (run s body))
      exact ⟨taint_Le_trans (taint_Le_join_left s _) h1, h2⟩

/-- A loop's analysis result is a fixpoint: above the entry state and stable under the body. -/
theorem taint_while_postfix (s : State) (c : Bil.Exp) (body : List Bil.Stmt) :
    taint_Le s (stmt s (.while c body)) ∧
      taint_Le (run (stmt s (.while c body)) body) (stmt s (.while c body)) := by
  rw [taint_stmt_while]
  exact taint_loopState_postfix body _ s

/-! ### Soundness against execution -/

/-- The address a concrete evaluation resolves `a` to. -/
def taint_address (env : Bil.Env) (a : Bil.Exp) : Option (Σ width, BitVec width) :=
  match Bil.evalExp env a with
  | .ok value => (Bap.Value.asBits value).toOption
  | .error _ => none

/-- Whether the condition of an `ite` selects its first arm. -/
def taint_taken (env : Bil.Env) (c : Bil.Exp) : Bool :=
  match Bil.evalExp env c with
  | .ok (.bits value) => value.toNat == 1
  | _ => false

/-- The labels of a value on one concrete execution: loads read the bytes of the address actually
computed, and an `ite` carries the labels of the arm actually taken. Data flow only, as the analysis:
a condition or a load address contributes nothing, so implicit flows and pointer taint are out of
scope. A `let` body reads a shadowed variable's state labels; the bound value's labels are added. -/
def taint_concreteExp (T : State) : Bil.Env → Bil.Exp → Labels
  | _, .int _ => []
  | _, .var v => labelsOfVar T v
  | env, .load m a _ size =>
    union (taint_concreteExp T env m) <|
      match taint_address env a with
      | some address => (bytes address size).flatMap (labelsOfMemory T)
      | none => []
  | env, .store m a v _ _ =>
    union (taint_concreteExp T env m) (union (taint_concreteExp T env a) (taint_concreteExp T env v))
  | env, .bin _ l r => union (taint_concreteExp T env l) (taint_concreteExp T env r)
  | env, .un _ v => taint_concreteExp T env v
  | env, .cast _ _ v => taint_concreteExp T env v
  | env, .letIn x v b =>
    union (taint_concreteExp T env v) <|
      match Bil.evalExp env v with
      | .ok value => taint_concreteExp T (Bil.bind env x value) b
      | .error _ => []
  | env, .ite c y n =>
    if taint_taken env c then taint_concreteExp T env y else taint_concreteExp T env n
  | env, .extract _ _ v => taint_concreteExp T env v
  | env, .concat l r => union (taint_concreteExp T env l) (taint_concreteExp T env r)
  | _, .unknown _ _ => []

/-- The taint effect of assigning `e` to memory variable `dst`, writing the bytes actually addressed. -/
def taint_concreteStore (dst : Bap.Var) (T : State) (env : Bil.Env) : Bil.Exp → State
  | .store m a v _ size =>
    let labels := union (taint_concreteExp T env a) (taint_concreteExp T env v)
    let inner := taint_concreteStore dst T env m
    match taint_address env a with
    | some address => (bytes address size).foldl (fun state byte => putMemory byte labels state) inner
    | none => inner
  | .var source => if source = dst then T else putVar dst (labelsOfVar T source) T
  | other => putVar dst (taint_concreteExp T env other) T

mutual
  /-- `Bil.execStmt` that also tracks byte-exact taint along the path it takes. -/
  def taint_execStmt (fuel : Nat) (st : Bil.State) (T : State) (s : Bil.Stmt) :
      Except String (Bil.State × State × Bil.Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match s with
      | .move var value => do
        let result ← Bil.execExp st value
        let T := match value with
          | .store .. => taint_concreteStore var T st.env value
          | _ => putVar var (taint_concreteExp T st.env value) T
        .ok ({ env := Bil.bind st.env var result }, T, .normal)
      | .jmp target => do
        let target ← Value.asBits (← Bil.execExp st target)
        .ok (st, T, .jump target.2)
      | .special message => .ok (st, T, .special message)
      | .cpuExn number => .ok (st, T, .cpuExn number)
      | .ifElse condition yes no => do
        let ⟨width, condition⟩ ← Value.asBits (← Bil.execExp st condition)
        if h : width = 1 then
          let condition : BitVec 1 := h ▸ condition
          taint_execProgram fuel st T (if condition = 1 then yes else no)
        else
          .error "condition must be one bit"
      | .while condition body => do
        let ⟨width, conditionValue⟩ ← Value.asBits (← Bil.execExp st condition)
        if h : width = 1 then
          let conditionValue : BitVec 1 := h ▸ conditionValue
          if conditionValue = 1 then
            let (next, T, effect) ← taint_execProgram fuel st T body
            match effect with
            | .normal => taint_execStmt fuel next T (.while condition body)
            | other => .ok (next, T, other)
          else
            .ok (st, T, .normal)
        else
          .error "condition must be one bit"

  /-- `Bil.execProgram` that also tracks byte-exact taint. -/
  def taint_execProgram (fuel : Nat) (st : Bil.State) (T : State) (program : Bil.Program) :
      Except String (Bil.State × State × Bil.Effect) :=
    match fuel with
    | 0 => .error "execution fuel exhausted"
    | fuel + 1 =>
      match program with
      | [] => .ok (st, T, .normal)
      | s :: rest => do
        let (next, T, effect) ← taint_execStmt fuel st T s
        match effect with
        | .normal => taint_execProgram fuel next T rest
        | other => .ok (next, T, other)
end

/-- Forgets the taint of an instrumented result. -/
private def taint_forget (r : Except String (Bil.State × State × Bil.Effect)) :
    Except String (Bil.State × Bil.Effect) :=
  match r with
  | .ok (st, _, e) => .ok (st, e)
  | .error m => .error m

/-- The instrumented semantics takes exactly the path of `Bil`, with the same results and errors. -/
theorem taint_exec_faithful (fuel : Nat) :
    (∀ st T s, taint_forget (taint_execStmt fuel st T s) = Bil.execStmt fuel st s) ∧
      ∀ st T code, taint_forget (taint_execProgram fuel st T code) = Bil.execProgram fuel st code := by
  induction fuel with
  | zero => exact ⟨by intros; simp [taint_execStmt, Bil.execStmt, taint_forget], by
      intros; simp [taint_execProgram, Bil.execProgram, taint_forget]⟩
  | succ f ih =>
    obtain ⟨is, ip⟩ := ih
    constructor
    · intro st T s
      cases s with
      | move v e =>
        simp only [taint_execStmt, Bil.execStmt]
        cases Bil.execExp st e <;> rfl
      | jmp t =>
        simp only [taint_execStmt, Bil.execStmt]
        cases Bil.execExp st t with
        | error _ => rfl
        | ok r => cases hb : Value.asBits r <;> simp [hb, bind, Except.bind, taint_forget]
      | special m => rfl
      | cpuExn n => rfl
      | ifElse c y n =>
        simp only [taint_execStmt, Bil.execStmt]
        cases Bil.execExp st c with
        | error _ => rfl
        | ok r =>
          cases hb : Value.asBits r with
          | error _ => simp [hb, bind, Except.bind, taint_forget]
          | ok b =>
            rcases b with ⟨w, cv⟩
            simp only [hb, bind, Except.bind]
            by_cases hw : w = 1
            · subst hw
              simpa using ip st T _
            · simp [hw, taint_forget]
      | «while» c body =>
        simp only [taint_execStmt, Bil.execStmt]
        cases Bil.execExp st c with
        | error _ => rfl
        | ok r =>
          cases hb : Value.asBits r with
          | error _ => simp [hb, bind, Except.bind, taint_forget]
          | ok b =>
            rcases b with ⟨w, cv⟩
            simp only [hb, bind, Except.bind]
            by_cases hw : w = 1
            · subst hw
              simp only [dite_true]
              split
              · rw [← ip st T body]
                cases taint_execProgram f st T body with
                | error _ => rfl
                | ok r =>
                  rcases r with ⟨next, T', e⟩
                  cases e with
                  | normal => simpa [taint_forget] using is next T' _
                  | _ => rfl
              · rfl
            · simp [hw, taint_forget]
    · intro st T code
      cases code with
      | nil => rfl
      | cons s rest =>
        simp only [taint_execProgram, Bil.execProgram]
        rw [← is st T s]
        cases taint_execStmt f st T s with
        | error _ => rfl
        | ok r =>
          rcases r with ⟨next, T', e⟩
          cases e with
          | normal => simpa [taint_forget, bind, Except.bind] using ip next T' rest
          | _ => rfl

private theorem taint_address_of_constant {a : Bil.Exp} {x : Σ width, BitVec width} (env : Bil.Env)
    (h : constant a = some x) : taint_address env a = some x := by
  unfold constant at h
  unfold taint_address
  cases he : Bil.evalExp [] a with
  | error _ => rw [he] at h; cases h
  | ok r =>
    rw [he] at h
    rw [taint_eval_closed env he]
    exact h

private theorem taint_concreteExp_subset {T S : State} (h : taint_Le T S) (e : Bil.Exp) :
    ∀ env, taint_concreteExp T env e ⊆ exp S e := by
  induction e with
  | int _ => intro env; simp [taint_concreteExp]
  | var v => intro env; simpa [taint_concreteExp, exp] using h.1 v
  | load m ad _ size im _ =>
    intro env
    simp only [taint_concreteExp, exp]
    refine taint_union_mono (im env) ?_
    cases hc : constant ad with
    | some x =>
      rw [taint_address_of_constant env hc]
      intro n hn
      simp only [List.mem_eraseDups, List.mem_flatMap] at hn ⊢
      rcases hn with ⟨k, hk, hn⟩
      exact ⟨k, hk, h.2.1 k hn⟩
    | none =>
      cases taint_address env ad with
      | none => simp
      | some x =>
        intro n hn
        simp only [List.mem_flatMap] at hn
        rcases hn with ⟨k, _, hn⟩
        exact taint_labelsOfMemory_subset_memoryLabels S k (h.2.1 k hn)
  | store _ _ _ _ _ im ia iv =>
    intro env
    simp only [taint_concreteExp, exp]
    exact taint_union_mono (im env) (taint_union_mono (ia env) (iv env))
  | bin _ _ _ il ir =>
    intro env
    simp only [taint_concreteExp, exp]
    exact taint_union_mono (il env) (ir env)
  | concat _ _ il ir =>
    intro env
    simp only [taint_concreteExp, exp]
    exact taint_union_mono (il env) (ir env)
  | un _ _ i => intro env; simpa only [taint_concreteExp, exp] using i env
  | cast _ _ _ i => intro env; simpa only [taint_concreteExp, exp] using i env
  | extract _ _ _ i => intro env; simpa only [taint_concreteExp, exp] using i env
  | letIn x v b iv ib =>
    intro env
    simp only [taint_concreteExp, exp]
    refine taint_union_mono (iv env) ?_
    cases Bil.evalExp env v with
    | error _ => simp
    | ok r => exact ib _
  | ite c _ _ _ iy in_ =>
    intro env n hn
    simp only [taint_concreteExp, exp] at hn ⊢
    split at hn
    · exact (taint_mem_union _ _ _).mpr (Or.inl (iy env hn))
    · exact (taint_mem_union _ _ _).mpr (Or.inr (in_ env hn))
  | unknown _ _ => intro env; simp [taint_concreteExp]

private theorem taint_concreteStore_le {T S : State} (h : taint_Le T S) (dst : Bap.Var) (env : Bil.Env)
    (e : Bil.Exp) : taint_Le (taint_concreteStore dst T env e) (store dst S e) := by
  have hexp := taint_concreteExp_subset h
  induction e with
  | store m ad val en z im _ _ =>
    rw [taint_store_store]
    simp only [taint_concreteStore]
    have hl : union (taint_concreteExp T env ad) (taint_concreteExp T env val) ⊆
        union (exp S ad) (exp S val) := taint_union_mono (hexp _ env) (hexp _ env)
    cases hc : constant ad with
    | some x =>
      rw [taint_address_of_constant env hc]
      exact taint_Le_putAll im _ hl
    | none =>
      simp only
      have hS : taint_Le (store dst S m)
          { store dst S m with anywhere := union (store dst S m).anywhere (union (exp S ad) (exp S val)) } := by
        refine ⟨fun _ _ k => k, fun w n hn => ?_, fun n hn => ?_⟩
        · rcases (taint_mem_labelsOfMemory _ w n).mp hn with hn | hn
          · exact (taint_mem_labelsOfMemory _ w n).mpr (Or.inl hn)
          · exact (taint_mem_labelsOfMemory _ w n).mpr
              (Or.inr ((taint_mem_union _ _ _).mpr (Or.inl hn)))
        · exact (taint_mem_union _ _ _).mpr (Or.inl hn)
      cases taint_address env ad with
      | none => exact taint_Le_trans im hS
      | some x =>
        refine taint_Le_putAll_left (taint_Le_trans im hS) _ fun n hn => ?_
        exact (taint_mem_union _ _ _).mpr (Or.inr (hl hn))
  | var source =>
    simp only [taint_concreteStore, store]
    split
    · exact h
    · exact taint_Le_putVar h _ (h.1 source)
  | _ =>
    simp only [taint_concreteStore, store]
    exact taint_Le_putVar h _ (hexp _ env)

mutual
  /-- `X` is the analysis state at a point where `s`, entered in state `S`, may leave the program by
  a jump, `special` or CPU exception. -/
  inductive taint_ExitAt : State → Bil.Stmt → State → Prop
    | jmp (S t) : taint_ExitAt S (.jmp t) S
    | special (S m) : taint_ExitAt S (.special m) S
    | cpuExn (S n) : taint_ExitAt S (.cpuExn n) S
    | loop (S c b X) : taint_ExitIn (stmt S (.while c b)) b X → taint_ExitAt S (.while c b) X
    | yes (S c y n X) : taint_ExitIn S y X → taint_ExitAt S (.ifElse c y n) X
    | no (S c y n X) : taint_ExitIn S n X → taint_ExitAt S (.ifElse c y n) X

  /-- As `taint_ExitAt`, for a statement list. -/
  inductive taint_ExitIn : State → List Bil.Stmt → State → Prop
    | head (S s rest X) : taint_ExitAt S s X → taint_ExitIn S (s :: rest) X
    | tail (S s rest X) : taint_ExitIn (stmt S s) rest X → taint_ExitIn S (s :: rest) X
end

/-- Splits a postcondition on whether execution falls through or leaves the program. -/
def taint_Post (effect : Bil.Effect) (normal leaves : Prop) : Prop :=
  match effect with
  | .normal => normal
  | _ => leaves

private theorem taint_sim (fuel : Nat) :
    (∀ st T S s st' T' e, taint_Le T S → taint_execStmt fuel st T s = .ok (st', T', e) →
      taint_Post e (taint_Le T' (stmt S s)) (∃ X, taint_ExitAt S s X ∧ taint_Le T' X)) ∧
    (∀ st T S code st' T' e, taint_Le T S → taint_execProgram fuel st T code = .ok (st', T', e) →
      taint_Post e (taint_Le T' (run S code)) (∃ X, taint_ExitIn S code X ∧ taint_Le T' X)) ∧
    (∀ R c body, taint_Le (run R body) R → ∀ st T st' T' e, taint_Le T R →
      taint_execStmt fuel st T (.while c body) = .ok (st', T', e) →
      taint_Post e (taint_Le T' R) (∃ X, taint_ExitIn R body X ∧ taint_Le T' X)) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [taint_execStmt, taint_execProgram]
  | succ f ih =>
    obtain ⟨is, ip, iw⟩ := ih
    have hwhile : ∀ R c body, taint_Le (run R body) R → ∀ st T st' T' e, taint_Le T R →
        taint_execStmt (f + 1) st T (.while c body) = .ok (st', T', e) →
        taint_Post e (taint_Le T' R) (∃ X, taint_ExitIn R body X ∧ taint_Le T' X) := by
      intro R c body hR st T st' T' e hT h
      simp only [taint_execStmt] at h
      cases he : Bil.execExp st c with
      | error _ => simp [he, bind, Except.bind] at h
      | ok r =>
        cases hb : Value.asBits r with
        | error _ => simp [he, hb, bind, Except.bind] at h
        | ok b =>
          rcases b with ⟨w, cv⟩
          simp only [he, hb, bind, Except.bind] at h
          by_cases hw : w = 1
          · subst hw
            simp only [dite_true] at h
            split at h
            · cases hp : taint_execProgram f st T body with
              | error _ => simp [hp] at h
              | ok p =>
                rcases p with ⟨next, T1, eff⟩
                simp only [hp] at h
                have hpost := ip st T R body next T1 eff hT hp
                cases eff with
                | normal => exact iw R c body hR next T1 st' T' e (taint_Le_trans hpost hR) h
                | jump t =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact hpost
                | special m =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact hpost
                | cpuExn n =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact hpost
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact hT
          · simp [hw] at h
    have hstmt : ∀ st T S s st' T' e, taint_Le T S → taint_execStmt (f + 1) st T s = .ok (st', T', e) →
        taint_Post e (taint_Le T' (stmt S s)) (∃ X, taint_ExitAt S s X ∧ taint_Le T' X) := by
      intro st T S s st' T' e hT h
      cases s with
      | move v value =>
        simp only [taint_execStmt] at h
        cases he : Bil.execExp st value with
        | error _ => simp [he, bind, Except.bind] at h
        | ok r =>
          simp only [he, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          show taint_Le _ _
          cases value with
          | store m ad val en z =>
            rw [taint_stmt_store]
            exact taint_concreteStore_le hT v st.env _
          | _ =>
            simp only [stmt]
            exact taint_Le_putVar hT v (taint_concreteExp_subset hT _ st.env)
      | jmp t =>
        simp only [taint_execStmt] at h
        cases he : Bil.execExp st t with
        | error _ => simp [he, bind, Except.bind] at h
        | ok r =>
          cases hb : Value.asBits r with
          | error _ => simp [he, hb, bind, Except.bind] at h
          | ok b =>
            simp only [he, hb, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨S, .jmp S t, hT⟩
      | special m =>
        simp only [taint_execStmt, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨S, .special S m, hT⟩
      | cpuExn n =>
        simp only [taint_execStmt, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨S, .cpuExn S n, hT⟩
      | «while» c body =>
        obtain ⟨h1, h2⟩ := taint_while_postfix S c body
        have := hwhile (stmt S (.while c body)) c body h2 st T st' T' e (taint_Le_trans hT h1) h
        cases e with
        | normal => exact this
        | jump t =>
          obtain ⟨X, hX, hle⟩ := this
          exact ⟨X, .loop S c body X hX, hle⟩
        | special m =>
          obtain ⟨X, hX, hle⟩ := this
          exact ⟨X, .loop S c body X hX, hle⟩
        | cpuExn n =>
          obtain ⟨X, hX, hle⟩ := this
          exact ⟨X, .loop S c body X hX, hle⟩
      | ifElse c y n =>
        simp only [taint_execStmt] at h
        cases he : Bil.execExp st c with
        | error _ => simp [he, bind, Except.bind] at h
        | ok r =>
          cases hb : Value.asBits r with
          | error _ => simp [he, hb, bind, Except.bind] at h
          | ok b =>
            rcases b with ⟨w, cv⟩
            simp only [he, hb, bind, Except.bind] at h
            by_cases hw : w = 1
            · subst hw
              simp only [dite_true] at h
              rw [taint_stmt_ifElse]
              split at h
              · have hpost := ip st T S y st' T' e hT h
                cases e with
                | normal => exact taint_Le_trans hpost (taint_Le_join_left _ _)
                | jump t =>
                  obtain ⟨X, hX, hle⟩ := hpost
                  exact ⟨X, .yes S c y n X hX, hle⟩
                | special m =>
                  obtain ⟨X, hX, hle⟩ := hpost
                  exact ⟨X, .yes S c y n X hX, hle⟩
                | cpuExn k =>
                  obtain ⟨X, hX, hle⟩ := hpost
                  exact ⟨X, .yes S c y n X hX, hle⟩
              · have hpost := ip st T S n st' T' e hT h
                cases e with
                | normal => exact taint_Le_trans hpost (taint_Le_join_right _ _)
                | jump t =>
                  obtain ⟨X, hX, hle⟩ := hpost
                  exact ⟨X, .no S c y n X hX, hle⟩
                | special m =>
                  obtain ⟨X, hX, hle⟩ := hpost
                  exact ⟨X, .no S c y n X hX, hle⟩
                | cpuExn k =>
                  obtain ⟨X, hX, hle⟩ := hpost
                  exact ⟨X, .no S c y n X hX, hle⟩
            · simp [hw] at h
    refine ⟨hstmt, ?_, hwhile⟩
    intro st T S code st' T' e hT h
    cases code with
    | nil =>
      simp only [taint_execProgram, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      show taint_Le _ _
      rwa [taint_run_nil]
    | cons s rest =>
      simp only [taint_execProgram] at h
      cases hs : taint_execStmt f st T s with
      | error _ => simp [hs, bind, Except.bind] at h
      | ok p =>
        rcases p with ⟨next, T1, eff⟩
        simp only [hs, bind, Except.bind] at h
        have hpost := is st T S s next T1 eff hT hs
        cases eff with
        | normal =>
          have hrest := ip next T1 (stmt S s) rest st' T' e hpost h
          rw [taint_run_cons]
          cases e with
          | normal => exact hrest
          | jump t =>
            obtain ⟨X, hX, hle⟩ := hrest
            exact ⟨X, .tail S s rest X hX, hle⟩
          | special m =>
            obtain ⟨X, hX, hle⟩ := hrest
            exact ⟨X, .tail S s rest X hX, hle⟩
          | cpuExn n =>
            obtain ⟨X, hX, hle⟩ := hrest
            exact ⟨X, .tail S s rest X hX, hle⟩
        | jump t =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨X, hX, hle⟩ := hpost
          exact ⟨X, .head S s rest X hX, hle⟩
        | special m =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨X, hX, hle⟩ := hpost
          exact ⟨X, .head S s rest X hX, hle⟩
        | cpuExn n =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨X, hX, hle⟩ := hpost
          exact ⟨X, .head S s rest X hX, hle⟩

/-- Taint soundness against execution. Any real run of `code`, from a state whose taint `T` the
analysis state `S` covers, carries byte-exact taint through the path it takes (`taint_execProgram`,
which `taint_exec_faithful` shows takes the same path) and that taint is covered by the analysis: by
`run S code` when the run falls through, and when it leaves the program mid-way by the analysis state
at the leaving statement. Data flow only: see `taint_concreteExp`. -/
theorem taint_run_overapprox {fuel : Nat} {st st' : Bil.State} {e : Bil.Effect} {T S : State}
    {code : Bil.Program} (hT : taint_Le T S) (h : Bil.execProgram fuel st code = .ok (st', e)) :
    ∃ T', taint_execProgram fuel st T code = .ok (st', T', e) ∧
      taint_Post e (taint_Le T' (run S code)) (∃ X, taint_ExitIn S code X ∧ taint_Le T' X) := by
  have hf := (taint_exec_faithful fuel).2 st T code
  rw [h] at hf
  cases hr : taint_execProgram fuel st T code with
  | error m => rw [hr] at hf; cases hf
  | ok r =>
    rcases r with ⟨s, T', e'⟩
    rw [hr] at hf
    simp only [taint_forget, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨T', rfl, (taint_sim fuel).2.1 st T S code _ T' _ hT hr⟩

/-! ### The fixes, stated on the analysis -/

/-- A statement list with no loop, on which the analysis is monotone. Monotonicity across a loop is
not claimed: the iteration's fuel depends on its start state, and `saturate` coarsens on exhaustion. -/
inductive taint_LoopFree : Bil.Stmt → Prop
  | move (v e) : taint_LoopFree (.move v e)
  | jmp (t) : taint_LoopFree (.jmp t)
  | special (m) : taint_LoopFree (.special m)
  | cpuExn (n) : taint_LoopFree (.cpuExn n)
  | ifElse (c y n) : (∀ s ∈ y, taint_LoopFree s) → (∀ s ∈ n, taint_LoopFree s) →
      taint_LoopFree (.ifElse c y n)

private theorem taint_store_mono {a b : State} (h : taint_Le a b) (dst : Bap.Var) (e : Bil.Exp) :
    taint_Le (store dst a e) (store dst b e) := by
  induction e with
  | store m ad val en z im _ _ =>
    rw [taint_store_store, taint_store_store]
    have hl := taint_union_mono (taint_exp_mono h ad) (taint_exp_mono h val)
    cases constant ad with
    | some x => exact taint_Le_putAll im _ hl
    | none =>
      refine ⟨im.1, fun w n hn => ?_, fun n hn => ?_⟩
      · rcases (taint_mem_labelsOfMemory _ w n).mp hn with hn | hn
        · have : n ∈ labelsOfMemory (store dst b m) w :=
            im.2.1 w ((taint_mem_labelsOfMemory _ w n).mpr (Or.inl hn))
          rcases (taint_mem_labelsOfMemory _ w n).mp this with k | k
          · exact (taint_mem_labelsOfMemory _ w n).mpr (Or.inl k)
          · exact (taint_mem_labelsOfMemory _ w n).mpr (Or.inr ((taint_mem_union _ _ _).mpr (Or.inl k)))
        · refine (taint_mem_labelsOfMemory _ w n).mpr (Or.inr ?_)
          exact taint_union_mono im.2.2 hl hn
      · exact taint_union_mono im.2.2 hl hn
  | var source =>
    simp only [store]
    split
    · exact h
    · exact taint_Le_putVar h _ (h.1 source)
  | _ =>
    simp only [store]
    exact taint_Le_putVar h _ (taint_exp_mono h _)

private theorem taint_join_mono {a b c d : State} (h : taint_Le a c) (k : taint_Le b d) :
    taint_Le (join a b) (join c d) :=
  taint_join_le (taint_Le_trans h (taint_Le_join_left c d)) (taint_Le_trans k (taint_Le_join_right c d))

/-- On loop-free statements the transfer function is monotone. -/
theorem taint_stmt_mono {s : Bil.Stmt} (hs : taint_LoopFree s) :
    ∀ {a b}, taint_Le a b → taint_Le (stmt a s) (stmt b s) := by
  have runMono : ∀ {code : List Bil.Stmt},
      (∀ s ∈ code, ∀ {a b}, taint_Le a b → taint_Le (stmt a s) (stmt b s)) →
      ∀ {a b}, taint_Le a b → taint_Le (run a code) (run b code) := by
    intro code ih
    induction code with
    | nil => intro a b h; simpa [taint_run_nil] using h
    | cons x t it =>
      intro a b h
      rw [taint_run_cons, taint_run_cons]
      exact it (fun s hs => ih s (List.mem_cons_of_mem _ hs)) (ih x (by simp) h)
  induction s using stmtInduction with
  | move v e =>
    intro a b h
    by_cases he : ∀ m ad val en z, e ≠ .store m ad val en z
    · rw [taint_stmt_move _ _ _ he, taint_stmt_move _ _ _ he]
      exact taint_Le_putVar h v (taint_exp_mono h e)
    · simp only [ne_eq, Classical.not_forall, Classical.not_not] at he
      rcases he with ⟨m, ad, val, en, z, rfl⟩
      rw [taint_stmt_store, taint_stmt_store]
      exact taint_store_mono h v _
  | jmp _ => intro a b h; simpa [stmt] using h
  | special _ => intro a b h; simpa [stmt] using h
  | cpuExn _ => intro a b h; simpa [stmt] using h
  | while_ c body _ => cases hs
  | ifElse c y n iy in_ =>
    intro a b h
    cases hs with
    | ifElse _ _ _ hy hn =>
      rw [taint_stmt_ifElse, taint_stmt_ifElse]
      exact taint_join_mono (runMono (fun s m => iy s m (hy s m)) h) (runMono (fun s m => in_ s m (hn s m)) h)

theorem taint_run_mono {code : Bil.Program} (hc : ∀ s ∈ code, taint_LoopFree s) {a b : State}
    (h : taint_Le a b) : taint_Le (run a code) (run b code) := by
  induction code generalizing a b with
  | nil => simpa [taint_run_nil] using h
  | cons x t it =>
    rw [taint_run_cons, taint_run_cons]
    exact it (fun s hs => hc s (List.mem_cons_of_mem _ hs)) (taint_stmt_mono (hc x (by simp)) h)

/-- The analysis state after `n` passes over a loop body. -/
def taint_iterate (body : List Bil.Stmt) : Nat → State → State
  | 0, s => s
  | n + 1, s => taint_iterate body n (run s body)

/-- A loop's labels include those of every number of iterations of a loop-free body. -/
theorem taint_while_covers_iterations (S : State) (c : Bil.Exp) (body : List Bil.Stmt)
    (hb : ∀ s ∈ body, taint_LoopFree s) (n : Nat) :
    taint_Le (taint_iterate body n S) (stmt S (.while c body)) := by
  obtain ⟨h1, h2⟩ := taint_while_postfix S c body
  generalize stmt S (.while c body) = R at h1 h2
  induction n generalizing S with
  | zero => exact h1
  | succ n it => exact it _ (taint_Le_trans (taint_run_mono hb h1) h2)

/-- Taint reaches through a loop's later iterations: with `z` tainted, `x` receives `y` on the second
iteration of `while c { x := y; y := z }`. -/
theorem taint_while_second_iteration (x y z : Bap.Var) (c : Bil.Exp) (l : Nat) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    l ∈ labelsOfVar (stmt (sourceVar {} z [l]) (.while c [.move x (.var y), .move y (.var z)])) x := by
  have hb : ∀ s ∈ [Bil.Stmt.move x (.var y), .move y (.var z)], taint_LoopFree s := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact .move _ _
  refine (taint_while_covers_iterations _ c _ hb 2).1 x ?_
  have step : ∀ X : State, run X [.move x (.var y), .move y (.var z)] =
      putVar y (labelsOfVar (putVar x (labelsOfVar X y) X) z) (putVar x (labelsOfVar X y) X) := by
    intro X
    simp only [taint_run_cons, taint_run_nil]
    rw [taint_stmt_move _ _ _ (by intros; simp), taint_stmt_move _ _ _ (by intros; simp)]
    simp [exp]
  have hz : l ∈ labelsOfVar (sourceVar {} z [l]) z :=
    (taint_mem_labelsOfVar_sourceVar _ _ _ _ _).mpr (Or.inr ⟨rfl, by simp⟩)
  show l ∈ labelsOfVar (run (run (sourceVar {} z [l]) _) _) x
  rw [step, step]
  simp only [taint_labelsOfVar_putVar]
  have hzx : z ≠ x := fun e => hxz e.symm
  have hzy : z ≠ y := fun e => hyz e.symm
  simp [hxy, hzx, hzy, hz]

/-- A branch never loses taint: whatever either arm's analysis reports survives the join. -/
theorem taint_ifElse_var (S : State) (c : Bil.Exp) (y n : List Bil.Stmt) (v : Bap.Var) (l : Nat) :
    l ∈ labelsOfVar (stmt S (.ifElse c y n)) v ↔
      l ∈ labelsOfVar (run S y) v ∨ l ∈ labelsOfVar (run S n) v := by
  rw [taint_stmt_ifElse, taint_mem_labelsOfVar_join]

theorem taint_ifElse_memory (S : State) (c : Bil.Exp) (y n : List Bil.Stmt) (m l : Nat) :
    l ∈ labelsOfMemory (stmt S (.ifElse c y n)) m ↔
      l ∈ labelsOfMemory (run S y) m ∨ l ∈ labelsOfMemory (run S n) m := by
  rw [taint_stmt_ifElse, taint_mem_labelsOfMemory_join]

/-- A kill in one arm does not wipe taint the other arm keeps. -/
theorem taint_branch_kill_keeps (S : State) (c : Bil.Exp) (x : Bap.Var) (w : Nat) (value : BitVec w)
    (l : Nat) (h : l ∈ labelsOfVar S x) :
    l ∈ labelsOfVar (stmt S (.ifElse c [.move x (.int value)] [])) x := by
  rw [taint_ifElse_var, taint_run_nil]
  exact Or.inr h

/-- A load reads every byte of its width at a constant address, and what the address space wraps to. -/
theorem taint_load_covers_width (S : State) (m ad : Bil.Exp) (en : Endian) (z : Nat)
    {x : Σ width, BitVec width} (hc : constant ad = some x) {k : Nat} (hk : k ∈ bytes x z) :
    labelsOfMemory S k ⊆ exp S (.load m ad en z) := by
  intro n hn
  simp only [exp, hc, taint_mem_union, List.mem_eraseDups, List.mem_flatMap]
  exact Or.inr ⟨k, hk, hn⟩

/-- A load from an address that cannot be resolved may read any byte. -/
theorem taint_dynamic_load_reads_all (S : State) (m ad : Bil.Exp) (en : Endian) (z k : Nat)
    (hc : constant ad = none) : labelsOfMemory S k ⊆ exp S (.load m ad en z) := by
  intro n hn
  simp only [exp, hc, taint_mem_union]
  exact Or.inr (taint_labelsOfMemory_subset_memoryLabels S k hn)

/-- A store to a constant address writes the labels of its address and value over all its bytes,
strongly, and leaves other bytes alone. -/
theorem taint_store_spec (S : State) (v : Bap.Var) (ad val : Bil.Exp) (en : Endian) (z : Nat)
    {x : Σ width, BitVec width} (hc : constant ad = some x) (k : Nat) :
    labelsOfMemory (stmt S (.move v (.store (.var v) ad val en z))) k =
      if k ∈ bytes x z then union (union (exp S ad) (exp S val)) S.anywhere else labelsOfMemory S k := by
  rw [taint_stmt_store, taint_store_store, hc]
  simp only
  rw [taint_labelsOfMemory_putAll]
  simp [store]

/-- The labels a store with an unresolvable address writes are visible at every address. -/
theorem taint_dynamic_store_visible (S : State) (v : Bap.Var) (m ad val : Bil.Exp) (en : Endian) (z : Nat)
    (hc : constant ad = none) (k : Nat) :
    exp S val ⊆ labelsOfMemory (stmt S (.move v (.store m ad val en z))) k := by
  rw [taint_stmt_store, taint_store_store, hc]
  intro n hn
  exact (taint_mem_labelsOfMemory _ k n).mpr (Or.inr ((taint_mem_union _ _ _).mpr
    (Or.inr ((taint_mem_union _ _ _).mpr (Or.inr hn)))))

/-- A move transfers the source's labels to the destination and leaves every other variable alone. -/
theorem taint_move_spec (s : State) (v w : Bap.Var) (e : Bil.Exp)
    (he : ∀ m ad val en z, e ≠ .store m ad val en z) :
    labelsOfVar (stmt s (.move v e)) w = if w = v then exp s e else labelsOfVar s w := by
  rw [taint_stmt_move _ _ _ he, taint_labelsOfVar_putVar]

/-! ### Clean states -/

/-- Syntactic variable occurrences, including binders' bodies. -/
def taint_occurrences : Bil.Exp → List Bap.Var
  | .int _ | .unknown _ _ => []
  | .var v => [v]
  | .load m a _ _ => taint_occurrences m ++ taint_occurrences a
  | .store m a v _ _ => taint_occurrences m ++ taint_occurrences a ++ taint_occurrences v
  | .bin _ l r | .concat l r => taint_occurrences l ++ taint_occurrences r
  | .un _ v | .cast _ _ v | .extract _ _ v => taint_occurrences v
  | .letIn _ v b => taint_occurrences v ++ taint_occurrences b
  | .ite c y n => taint_occurrences c ++ taint_occurrences y ++ taint_occurrences n

private theorem taint_union_eq_nil {a b : Labels} (ha : a = []) (hb : b = []) : union a b = [] := by
  subst ha; subst hb; rfl

/-- Untainted operands stay untainted: with clean memory and clean variables, an expression is clean. -/
theorem taint_exp_clean (s : State) (e : Bil.Exp) (hm : ∀ a, labelsOfMemory s a = [])
    (hv : ∀ v ∈ taint_occurrences e, labelsOfVar s v = []) : exp s e = [] := by
  have hall : memoryLabels s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n hn
    simp only [memoryLabels, taint_mem_union, List.mem_flatMap] at hn
    rcases hn with ⟨k, _, hn⟩ | hn
    · have := (taint_mem_labelsOfMemory s k n).mpr (Or.inl hn)
      simp [hm] at this
    · have := (taint_mem_labelsOfMemory s 0 n).mpr (Or.inr hn)
      simp [hm] at this
  induction e with
  | int _ => rfl
  | var v => simpa [exp, taint_occurrences] using hv
  | load _ ad _ _ im _ =>
    simp only [taint_occurrences, List.mem_append] at hv
    simp only [exp]
    refine taint_union_eq_nil (im fun v h => hv v (Or.inl h)) ?_
    cases constant ad with
    | none => exact hall
    | some _ =>
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro n hn
      simp only [List.mem_eraseDups, List.mem_flatMap] at hn
      rcases hn with ⟨k, _, hn⟩
      simp [hm] at hn
  | store _ _ _ _ _ im ia iv =>
    simp only [taint_occurrences, List.mem_append] at hv
    exact taint_union_eq_nil (im fun v h => hv v (Or.inl (Or.inl h)))
      (taint_union_eq_nil (ia fun v h => hv v (Or.inl (Or.inr h))) (iv fun v h => hv v (Or.inr h)))
  | bin _ _ _ il ir | letIn _ _ _ il ir | concat _ _ il ir =>
    simp only [taint_occurrences, List.mem_append] at hv
    exact taint_union_eq_nil (il fun v h => hv v (Or.inl h)) (ir fun v h => hv v (Or.inr h))
  | un _ _ i | cast _ _ _ i | extract _ _ _ i =>
    simp only [taint_occurrences] at hv
    simpa only [exp] using i hv
  | ite _ _ _ _ iy in_ =>
    simp only [taint_occurrences, List.mem_append] at hv
    exact taint_union_eq_nil (iy fun v h => hv v (Or.inl (Or.inr h))) (in_ fun v h => hv v (Or.inr h))
  | unknown _ _ => rfl

/-- A completely clean state stays completely clean, whatever the program does. -/
theorem taint_run_clean (code : Bil.Program) : taint_labels (run {} code) = [] := by
  have := taint_run_provenance {} code
  exact List.eq_nil_iff_forall_not_mem.mpr fun n hn => by simpa [taint_labels] using this hn


end Taint

section Validate

set_option linter.unusedSimpArgs false

open Bap.Bil
open Bap.Analysis.Validate
open_private Bap.Analysis.Validate in Bap.Analysis.Validate :
  memoryEqual valueEq lookupEqual effectEq memoryVars

theorem validate_ok_iff (r : Result) :
    ok r = true ↔ r.effects = true ∧ r.registers = true ∧ r.memory = true ∧ r.continuation = true := by
  rcases r with ⟨a, b, c, d⟩
  simp [ok, Bool.and_assoc]

theorem validate_effectEq_refl (e : Effect) : effectEq e e = true := by
  cases e <;> simp [effectEq]

theorem validate_effectEq_symm (a b : Effect) : effectEq a b = effectEq b a := by
  cases a <;> cases b <;> simp [effectEq, eq_comm, Bool.and_comm]

/-- `effectEq` is exact equality of control-flow outcomes. -/
theorem validate_effectEq_sound {a b : Effect} (h : effectEq a b = true) : a = b := by
  cases a <;> cases b <;> simp [effectEq] at h ⊢
  · rename_i w v w' v'
    rcases h with ⟨rfl, hv⟩
    simpa using BitVec.eq_of_toNat_eq hv
  · exact h
  · exact h

/-- Every nonzero byte a memory reads at an address is listed in its cells at that address. -/
private theorem validate_mem_cells {w : Nat} (m : Memory w) (a : BitVec w)
    (h : Memory.readByte m a ≠ 0) : (a, Memory.readByte m a) ∈ Memory.cells m := by
  unfold Memory.readByte at h ⊢
  simp only [Std.TreeMap.get?_eq_getElem?] at h ⊢
  cases hp : m.pages[a.toNat / Memory.pageSize]? with
  | none => rw [hp] at h; exact absurd rfl h
  | some page =>
    rw [hp] at h
    have hb : a.toNat % Memory.pageSize < page.size := by
      refine Decidable.byContradiction fun hlt => h ?_
      exact getElem!_neg page _ hlt
    unfold Memory.cells
    refine List.mem_flatMap.mpr ⟨(a.toNat / Memory.pageSize, page), ?_, ?_⟩
    · exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hp
    · refine List.mem_filterMap.mpr ⟨a.toNat % Memory.pageSize, List.mem_range.mpr hb, ?_⟩
      simp only [h, ite_false]
      have : a.toNat / Memory.pageSize * Memory.pageSize + a.toNat % Memory.pageSize = a.toNat :=
        Nat.div_add_mod' _ _
      simp [this]

/-- Memories compare equal exactly when they read the same byte at every address. Pages holding
bytes past the address width alias, and only what `readByte` can see counts. -/
theorem validate_memoryEqual_iff {w : Nat} (left right : Memory w) :
    memoryEqual left right = true ↔ ∀ a, Memory.readByte left a = Memory.readByte right a := by
  simp only [memoryEqual, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h a
    by_cases hl : Memory.readByte left a = 0
    · by_cases hr : Memory.readByte right a = 0
      · rw [hl, hr]
      · exact h _ (List.mem_append_right _ (validate_mem_cells right a hr))
    · exact h _ (List.mem_append_left _ (validate_mem_cells left a hl))
  · intro h c _
    exact h c.1

theorem validate_memoryEqual_sound {w : Nat} {left right : Memory w}
    (h : memoryEqual left right = true) (a : BitVec w) :
    Memory.readByte left a = Memory.readByte right a :=
  (validate_memoryEqual_iff left right).mp h a

theorem validate_valueEq_refl_bits {w : Nat} (v : BitVec w) : valueEq (.bits v) (.bits v) = true := by
  simp [valueEq]

theorem validate_valueEq_undefined : valueEq .undefined .undefined = true := by
  simp [valueEq]

theorem validate_valueEq_memory_self {w : Nat} (m : Memory w) :
    valueEq (.memory m) (.memory m) = true := by
  simp only [valueEq, dite_true]
  exact (validate_memoryEqual_iff m m).mpr fun _ => rfl

/-- Value comparison is reflexive on every value. -/
theorem validate_valueEq_refl (value : Value) : valueEq value value = true := by
  cases value with
  | bits x => exact validate_valueEq_refl_bits x
  | memory m => exact validate_valueEq_memory_self m
  | undefined => exact validate_valueEq_undefined

/-- Equal memory values read the same bytes. -/
theorem validate_valueEq_memory_sound {w w' : Nat} {a : Memory w} {b : Memory w'}
    (h : valueEq (.memory a) (.memory b) = true) :
    ∃ hw : w = w', ∀ address, Memory.readByte a address = Memory.readByte (hw ▸ b) address := by
  simp only [valueEq] at h
  split at h
  · rename_i hw
    subst hw
    exact ⟨rfl, validate_memoryEqual_iff a b |>.mp h⟩
  · cases h

theorem validate_valueEq_bits_sound {w w' : Nat} {a : BitVec w} {b : BitVec w'}
    (h : valueEq (.bits a) (.bits b) = true) : (⟨w, a⟩ : Σ n, BitVec n) = ⟨w', b⟩ := by
  simp only [valueEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨rfl, hv⟩
  simp [BitVec.eq_of_toNat_eq hv]

private theorem validate_lookupEqual_self (env : Env) (v : Bap.Var) :
    lookupEqual v env env = true := by
  unfold lookupEqual
  cases lookup env v with
  | error => rfl
  | ok r => exact validate_valueEq_refl r

/-- The shape of a comparison when both runs succeed. -/
theorem validate_compare_ok {registers : List Bap.Var} {a b : Bil.Program} {init : State} {fuel : Nat}
    {sa sb : State} {ea eb : Effect}
    (ha : run a init fuel = .ok (sa, ea)) (hb : run b init fuel = .ok (sb, eb)) :
    compare registers a b init fuel = .ok {
      effects := effectEq ea eb
      registers := (registers ++ memoryVars sa ++ memoryVars sb).eraseDups.all
        fun v => lookupEqual v sa.env sb.env
      memory := (memoryVars sa ++ memoryVars sb).eraseDups.all fun v => lookupEqual v sa.env sb.env
      continuation := effectEq ea eb } := by
  unfold Bap.Analysis.Validate.compare
  rw [ha, hb]
  rfl

theorem validate_compare_error_left {registers : List Bap.Var} {a b : Bil.Program} {init : State}
    {fuel : Nat} {m : String} (ha : run a init fuel = .error m) :
    compare registers a b init fuel = .error m := by
  unfold Bap.Analysis.Validate.compare
  rw [ha]
  rfl

theorem validate_compare_error_right {registers : List Bap.Var} {a b : Bil.Program} {init : State}
    {fuel : Nat} {m : String} {r : State × Effect} (ha : run a init fuel = .ok r)
    (hb : run b init fuel = .error m) :
    compare registers a b init fuel = .error m := by
  rcases r with ⟨s, e⟩
  unfold Bap.Analysis.Validate.compare
  rw [ha, hb]
  rfl

private theorem validate_compare_cases {registers : List Bap.Var} {a b : Bil.Program} {init : State}
    {fuel : Nat} {r : Result} (h : compare registers a b init fuel = .ok r) :
    ∃ sa ea sb eb, run a init fuel = .ok (sa, ea) ∧ run b init fuel = .ok (sb, eb) := by
  cases ha : run a init fuel with
  | error m => rw [validate_compare_error_left ha] at h; cases h
  | ok ra =>
    cases hb : run b init fuel with
    | error m => rw [validate_compare_error_right ha hb] at h; cases h
    | ok rb => exact ⟨ra.1, ra.2, rb.1, rb.2, rfl, rfl⟩

/-- The `continuation` verdict always duplicates `effects`. -/
theorem validate_continuation_eq_effects {registers : List Bap.Var} {a b : Bil.Program} {init : State}
    {fuel : Nat} {r : Result} (h : compare registers a b init fuel = .ok r) :
    r.continuation = r.effects := by
  obtain ⟨sa, ea, sb, eb, ha, hb⟩ := validate_compare_cases h
  rw [validate_compare_ok ha hb] at h
  cases h
  rfl

/-- A program that runs always validates against itself. -/
theorem validate_compare_refl {registers : List Bap.Var} {a : Bil.Program} {init : State} {fuel : Nat}
    {s : State} {e : Effect} (ha : run a init fuel = .ok (s, e)) :
    ∃ r, compare registers a a init fuel = .ok r ∧ ok r = true := by
  refine ⟨_, validate_compare_ok ha ha, ?_⟩
  rw [validate_ok_iff]
  have hl := validate_lookupEqual_self s.env
  simp [validate_effectEq_refl, List.all_eq_true, hl]

/-- `compare` of a program with itself fails only if the program itself fails to run. -/
theorem validate_compare_self_error {registers : List Bap.Var} {a : Bil.Program} {init : State}
    {fuel : Nat} {m : String} (h : compare registers a a init fuel = .error m) :
    run a init fuel = .error m := by
  cases ha : run a init fuel with
  | error m' =>
    rw [validate_compare_error_left ha] at h
    cases h
    rfl
  | ok r =>
    rcases r with ⟨s, e⟩
    rw [validate_compare_ok ha ha] at h
    cases h

/-- Soundness: when the verdict holds, every listed register and control-flow effect agree. -/
theorem validate_compare_sound {registers : List Bap.Var} {a b : Bil.Program} {init : State} {fuel : Nat}
    {r : Result} (h : compare registers a b init fuel = .ok r) (hok : ok r = true) :
    ∃ sa sb e, run a init fuel = .ok (sa, e) ∧ run b init fuel = .ok (sb, e) ∧
      (∀ v ∈ registers, ∀ {w : Nat} (x : BitVec w), lookup sa.env v = .ok (.bits x) →
        ∃ y : BitVec w, lookup sb.env v = .ok (.bits y) ∧ y.toNat = x.toNat) ∧
      ∀ v ∈ registers, ∀ {w : Nat} (x : Memory w), lookup sa.env v = .ok (.memory x) →
        ∃ y : Memory w, lookup sb.env v = .ok (.memory y) ∧
          ∀ address, Memory.readByte x address = Memory.readByte y address := by
  obtain ⟨sa, ea, sb, eb, ha, hb⟩ := validate_compare_cases h
  rw [validate_compare_ok ha hb] at h
  cases h
  obtain ⟨he, hr, _, _⟩ := (validate_ok_iff _).mp hok
  have heq := validate_effectEq_sound he
  subst heq
  refine ⟨sa, sb, ea, ha, hb, ?_, ?_⟩
  · intro v hv w x hx
    have hall := List.all_eq_true.mp hr v (by simp [List.mem_eraseDups, hv])
    unfold lookupEqual at hall
    rw [hx] at hall
    cases hy : lookup sb.env v with
    | error m => rw [hy] at hall; simp at hall
    | ok y =>
      rw [hy] at hall
      cases y with
      | @bits w' y =>
        simp only [valueEq, Bool.and_eq_true, decide_eq_true_eq] at hall
        rcases hall with ⟨rfl, hv⟩
        exact ⟨y, rfl, hv.symm⟩
      | memory _ => simp [valueEq] at hall
      | undefined => simp [valueEq] at hall
  · intro v hv w x hx
    have hall := List.all_eq_true.mp hr v (by simp [List.mem_eraseDups, hv])
    unfold lookupEqual at hall
    rw [hx] at hall
    cases hy : lookup sb.env v with
    | error m => rw [hy] at hall; simp at hall
    | ok y =>
      rw [hy] at hall
      cases y with
      | bits _ => simp [valueEq] at hall
      | @memory w' y =>
        obtain ⟨rfl, hread⟩ := validate_valueEq_memory_sound hall
        exact ⟨y, rfl, hread⟩
      | undefined => simp [valueEq] at hall

/-- Comparing in the other order gives the same `effects` verdict. -/
theorem validate_compare_effects_symm {registers registers' : List Bap.Var} {a b : Bil.Program}
    {init : State} {fuel : Nat} {r : Result} (h : compare registers a b init fuel = .ok r) :
    ∃ r', compare registers' b a init fuel = .ok r' ∧ r'.effects = r.effects := by
  obtain ⟨sa, ea, sb, eb, ha, hb⟩ := validate_compare_cases h
  rw [validate_compare_ok ha hb] at h
  cases h
  exact ⟨_, validate_compare_ok hb ha, validate_effectEq_symm eb ea⟩

/-- Pages that alias under `addressWidth` no longer break reflexivity: the memory compares equal to
itself, and the empty program validates against itself from a state holding it. -/
theorem validate_compare_refl_aliased_memory {w : Nat} (pages : Std.TreeMap Nat ByteArray)
    (m : Bap.Var) (fuel : Nat) :
    ∃ r, Bap.Analysis.Validate.compare [] [] [] ⟨[(m, .memory (⟨pages⟩ : Memory w))]⟩ (fuel + 1) = .ok r ∧
      ok r = true := by
  have : run [] (⟨[(m, .memory (⟨pages⟩ : Memory w))]⟩ : State) (fuel + 1) =
      .ok (⟨[(m, .memory (⟨pages⟩ : Memory w))]⟩, .normal) := by
    simp [run, execProgram]
  exact validate_compare_refl this

end Validate

section StateMachine

open Bap.Analysis.StateMachine
open_private Bap.Analysis.StateMachine in Bap.Analysis.StateMachine : directTarget assignments simplerCandidates choose

theorem statemachine_transition_mem {result : Result} {value target : Nat}
    (h : transition result value = some target) : (⟨value, target⟩ : Case) ∈ result.cases := by
  simp only [transition, Option.map_eq_some_iff] at h
  rcases h with ⟨c, hc, rfl⟩
  have hm := List.mem_of_find?_eq_some hc
  have hv := List.find?_some hc
  simp at hv
  subst hv
  exact hm

/-- `transition` returns the first case for a value: an earlier matching case wins. -/
theorem statemachine_transition_first (stateVar : Option Bap.Var) (complete : Bool)
    (before after : List Case) (value target : Nat)
    (hb : ∀ c ∈ before, c.value ≠ value) :
    transition ⟨stateVar, before ++ ⟨value, target⟩ :: after, complete⟩ value = some target := by
  simp only [transition, List.find?_append]
  rw [List.find?_eq_none.mpr (by simpa using hb)]
  simp

theorem statemachine_transition_none_iff (result : Result) (value : Nat) :
    transition result value = none ↔ ∀ c ∈ result.cases, c.value ≠ value := by
  simp [transition, List.find?_eq_none]

theorem statemachine_mem_simplerCandidates {instructions : List Bap.Disasm.Insn}
    {triple : Bap.Var × Nat × Nat} :
    triple ∈ simplerCandidates instructions ↔
      ∃ index current next, instructions[index]? = some current ∧
        instructions[index + 1]? = some next ∧ directTarget next = some triple.2.2 ∧
        (triple.1, triple.2.1) ∈ assignments current := by
  simp only [simplerCandidates, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨index, hi, hm⟩
    split at hm
    · rename_i current next h1 h2
      split at hm
      · rename_i target ht
        simp only [List.mem_map] at hm
        rcases hm with ⟨a, ha, rfl⟩
        exact ⟨index, current, next, h1, h2, ht, ha⟩
      · simp at hm
    · simp at hm
  · rintro ⟨index, current, next, h1, h2, ht, ha⟩
    refine ⟨index, ?_, ?_⟩
    · have := (List.getElem?_eq_some_iff.mp h2).1
      omega
    · simp only [h1, h2, ht, List.mem_map]
      exact ⟨_, ha, rfl⟩

theorem statemachine_analyzeWithState_stateVar (instructions : List Bap.Disasm.Insn) (var : Bap.Var) :
    (analyzeWithState instructions var).stateVar = some var := rfl

/-- Every recovered case is backed by an assignment of the state variable immediately followed by
an instruction whose direct target is the case target. -/
theorem statemachine_analyzeWithState_evidence {instructions : List Bap.Disasm.Insn} {var : Bap.Var}
    {c : Case} (h : c ∈ (analyzeWithState instructions var).cases) :
    ∃ index current next, instructions[index]? = some current ∧
      instructions[index + 1]? = some next ∧ directTarget next = some c.target ∧
      (var, c.value) ∈ assignments current := by
  simp only [analyzeWithState, List.mem_filterMap] at h
  rcases h with ⟨triple, ht, he⟩
  split at he
  · rename_i hv
    simp only [Option.some.injEq] at he
    subst he
    rcases statemachine_mem_simplerCandidates.mp ht with ⟨index, current, next, h1, h2, h3, h4⟩
    refine ⟨index, current, next, h1, h2, h3, ?_⟩
    rw [← hv]
    exact h4
  · simp at he

/-- Conversely, every such adjacent pair produces a case. -/
theorem statemachine_analyzeWithState_complete {instructions : List Bap.Disasm.Insn} {var : Bap.Var}
    {index value target : Nat} {current next : Bap.Disasm.Insn}
    (h1 : instructions[index]? = some current) (h2 : instructions[index + 1]? = some next)
    (h3 : directTarget next = some target) (h4 : (var, value) ∈ assignments current) :
    (⟨value, target⟩ : Case) ∈ (analyzeWithState instructions var).cases := by
  simp only [analyzeWithState, List.mem_filterMap]
  refine ⟨(var, value, target), statemachine_mem_simplerCandidates.mpr
    ⟨index, current, next, h1, h2, h3, h4⟩, by simp⟩

theorem statemachine_mem_assignments {insn : Bap.Disasm.Insn} {var : Bap.Var} {value : Nat}
    (h : (var, value) ∈ assignments insn) :
    ∃ exp result, Bap.Bil.Stmt.move var exp ∈ insn.bil ∧ Bap.Bil.evalExp [] exp = .ok result ∧
      ((Bap.Value.asBits result).toOption.map fun bits => bits.2.toNat) = some value := by
  simp only [assignments, List.mem_filterMap] at h
  rcases h with ⟨stmt, hs, he⟩
  cases stmt with
  | move dst exp =>
    simp only at he
    split at he
    · rename_i result hr
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
      rcases he with ⟨bits, hb, rfl, rfl⟩
      exact ⟨exp, result, hs, hr, by simp [hb]⟩
    · simp at he
  | _ => simp at he

private def statemachine_casesOf (triples : List (Bap.Var × Nat × Nat)) (var : Bap.Var) : List Case :=
  (triples.filter fun triple => triple.1 = var).map fun triple => ⟨triple.2.1, triple.2.2⟩

private def statemachine_step (triples : List (Bap.Var × Nat × Nat))
    (best : Option (Bap.Var × List Case)) (var : Bap.Var) : Option (Bap.Var × List Case) :=
  match best with
  | some current =>
    if current.2.length < (statemachine_casesOf triples var).length then
      some (var, statemachine_casesOf triples var)
    else best
  | none => some (var, statemachine_casesOf triples var)

/-- The fold keeps the earlier best or a candidate, and is never smaller than any candidate seen. -/
private theorem statemachine_step_fold (triples : List (Bap.Var × Nat × Nat)) (vars : List Bap.Var)
    (init : Option (Bap.Var × List Case)) (final : Bap.Var × List Case)
    (h : vars.foldl (statemachine_step triples) init = some final) :
    (init = some final ∨ ∃ var ∈ vars, final = (var, statemachine_casesOf triples var)) ∧
    (∀ var ∈ vars, (statemachine_casesOf triples var).length ≤ final.2.length) ∧
    (∀ old, init = some old → old.2.length ≤ final.2.length) := by
  induction vars generalizing init with
  | nil =>
    simp only [List.foldl_nil] at h
    subst h
    refine ⟨.inl rfl, by simp, ?_⟩
    intro old ho
    cases ho
    omega
  | cons head tail ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with ⟨i1, i2, i3⟩
    cases init with
    | none =>
      refine ⟨?_, ?_, by simp⟩
      · rcases i1 with h1 | ⟨var, hv, h1⟩
        · cases h1
          exact .inr ⟨head, by simp, rfl⟩
        · exact .inr ⟨var, by simp [hv], h1⟩
      · intro var hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact i3 _ rfl
        · exact i2 _ hv
    | some old =>
      by_cases hlt : old.2.length < (statemachine_casesOf triples head).length
      · have hs : statemachine_step triples (some old) head =
            some (head, statemachine_casesOf triples head) := by simp [statemachine_step, hlt]
        rw [hs] at i1 i3
        have hl := i3 _ rfl
        simp only at hl
        refine ⟨?_, ?_, ?_⟩
        · rcases i1 with h1 | ⟨var, hv, h1⟩
          · cases h1
            exact .inr ⟨head, by simp, rfl⟩
          · exact .inr ⟨var, by simp [hv], h1⟩
        · intro var hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hl
          · exact i2 _ hv
        · intro o ho
          cases ho
          omega
      · have hs : statemachine_step triples (some old) head = some old := by
          simp [statemachine_step, hlt]
        rw [hs] at i1 i3
        have hl := i3 _ rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases i1 with h1 | ⟨var, hv, h1⟩
          · exact .inl h1
          · exact .inr ⟨var, by simp [hv], h1⟩
        · intro var hv
          rcases List.mem_cons.mp hv with rfl | hv
          · omega
          · exact i2 _ hv
        · intro o ho
          cases ho
          exact hl

private theorem statemachine_step_fold_some (triples : List (Bap.Var × Nat × Nat)) (head : Bap.Var)
    (tail : List Bap.Var) :
    ((head :: tail).foldl (statemachine_step triples) none).isSome := by
  have aux : ∀ (vars : List Bap.Var) (init : Option (Bap.Var × List Case)), init.isSome →
      (vars.foldl (statemachine_step triples) init).isSome := by
    intro vars
    induction vars with
    | nil => simp
    | cons x xs ih =>
      intro init hi
      apply ih
      cases init with
      | none => simp at hi
      | some old =>
        simp only [statemachine_step]
        split <;> simp
  exact aux tail _ (by simp [statemachine_step])

private theorem statemachine_choose_eq (instructions : List Bap.Disasm.Insn) :
    choose instructions = ((simplerCandidates instructions).map Prod.fst).eraseDups.foldl
      (statemachine_step (simplerCandidates instructions)) none := rfl

private theorem statemachine_casesOf_eq (instructions : List Bap.Disasm.Insn) (var : Bap.Var) :
    (analyzeWithState instructions var).cases =
      statemachine_casesOf (simplerCandidates instructions) var := by
  simp only [analyzeWithState, statemachine_casesOf]
  generalize simplerCandidates instructions = triples
  induction triples with
  | nil => rfl
  | cons head tail ih =>
    by_cases h : head.1 = var <;> simp [h, ih]

theorem statemachine_analyze_empty {instructions : List Bap.Disasm.Insn}
    (h : simplerCandidates instructions = []) :
    (analyze instructions).stateVar = none ∧ (analyze instructions).cases = [] ∧
      (analyze instructions).complete = false := by
  simp [analyze, choose, h]

/-- `analyze` finds a state variable exactly when some adjacent assignment/target pair exists. -/
theorem statemachine_analyze_stateVar_none_iff (instructions : List Bap.Disasm.Insn) :
    (analyze instructions).stateVar = none ↔ simplerCandidates instructions = [] := by
  constructor
  · intro h
    cases hl0 : simplerCandidates instructions with
    | nil => rfl
    | cons x xs =>
    have hx : x ∈ simplerCandidates instructions := by simp [hl0]
    have hv : x.1 ∈ ((simplerCandidates instructions).map Prod.fst).eraseDups :=
      List.mem_eraseDups.mpr (List.mem_map_of_mem hx)
    cases hl : ((simplerCandidates instructions).map Prod.fst).eraseDups with
    | nil => simp [hl] at hv
    | cons head tail =>
      have hs := statemachine_step_fold_some (simplerCandidates instructions) head tail
      rw [← hl, ← statemachine_choose_eq] at hs
      cases hc : choose instructions with
      | none => simp [hc] at hs
      | some best =>
        simp [analyze, hc] at h
  · intro h
    exact (statemachine_analyze_empty h).1

/-- When `analyze` chooses a variable, its cases are the ones `analyzeWithState` computes for it,
and no other candidate variable has more cases. -/
theorem statemachine_analyze_chosen {instructions : List Bap.Disasm.Insn} {var : Bap.Var}
    (h : (analyze instructions).stateVar = some var) :
    (analyze instructions).cases = (analyzeWithState instructions var).cases ∧
      (analyze instructions).complete = (analyzeWithState instructions var).complete ∧
      ∀ triple ∈ simplerCandidates instructions,
        (analyzeWithState instructions triple.1).cases.length ≤ (analyze instructions).cases.length := by
  cases hc : choose instructions with
  | none => simp [analyze, hc] at h
  | some best =>
    rcases best with ⟨chosen, cases⟩
    have hf := statemachine_step_fold _ _ _ _ ((statemachine_choose_eq instructions).symm.trans hc)
    rcases hf with ⟨h1, h2, _⟩
    rcases h1 with h1 | ⟨v, _, h1⟩
    · cases h1
    · simp only [Prod.mk.injEq] at h1
      rcases h1 with ⟨rfl, rfl⟩
      simp only [analyze, hc, Option.some.injEq] at h
      subst h
      have hw := statemachine_casesOf_eq instructions
      simp only [analyze, hc]
      refine ⟨(hw _).symm, ?_, ?_⟩
      · simp only [analyzeWithState] at hw ⊢
        rw [hw]
      · intro triple ht
        rw [hw]
        exact h2 _ (List.mem_eraseDups.mpr (List.mem_map_of_mem ht))

theorem statemachine_isFlattened_iff (result : Result) :
    isFlattened result = true ↔ result.complete = true ∧ 2 ≤ result.cases.length := by
  simp [isFlattened]

/-- Whichever way the variable was picked, completeness rules out indirect jumps. -/
theorem statemachine_analyzeWithState_complete_iff (instructions : List Bap.Disasm.Insn) (var : Bap.Var) :
    (analyzeWithState instructions var).complete = true ↔
      2 ≤ (analyzeWithState instructions var).cases.length ∧
        ∀ insn ∈ instructions, insn.flow ≠ .indirectJump := by
  simp [analyzeWithState]

theorem statemachine_analyze_complete_no_indirect {instructions : List Bap.Disasm.Insn}
    (h : (analyze instructions).complete = true) :
    2 ≤ (analyze instructions).cases.length ∧ ∀ insn ∈ instructions, insn.flow ≠ .indirectJump := by
  simp only [analyze] at h ⊢
  split at h
  · simp at h
  · simp_all

end StateMachine

section Deflatten

open Bap.Analysis.Deflatten
open_private Bap.Analysis.Deflatten in Bap.Analysis.Deflatten : assigns assignmentAddresses

private def deflatten_machine (instructions : List Bap.Disasm.Insn) (stateVar : Option Bap.Var) :
    Bap.Analysis.StateMachine.Result :=
  match stateVar with
  | some var => Bap.Analysis.StateMachine.analyzeWithState instructions var
  | none => Bap.Analysis.StateMachine.analyze instructions

private theorem deflatten_recover_of_none {instructions : List Bap.Disasm.Insn} {stateVar : Option Bap.Var}
    (h : (deflatten_machine instructions stateVar).stateVar = none) (entry : Nat) (external : List Nat) :
    recover entry instructions external stateVar = { disasm := { entry, instructions } } := by
  change (match (deflatten_machine instructions stateVar).stateVar with
    | none => _
    | some _ => _) = _
  rw [h]

private theorem deflatten_recover_of_some {instructions : List Bap.Disasm.Insn} {stateVar : Option Bap.Var}
    {var : Bap.Var} (h : (deflatten_machine instructions stateVar).stateVar = some var)
    (entry : Nat) (external : List Nat) :
    let machine := deflatten_machine instructions stateVar
    let addresses := instructions.map Bap.Disasm.Insn.address
    let missing := machine.cases.filter
      (fun current => !addresses.contains current.target && !external.contains current.target)
    let assignments := assignmentAddresses instructions var machine.cases
    let direct := machine.cases.flatMap fun current =>
      (assignmentAddresses instructions var [current]).map fun source => (source, current.target)
    let remaining := instructions.flatMap fun insn =>
      if assignments.contains insn.address || insn.flow = .indirectJump then []
      else insn.successors.map (insn.address, ·)
    recover entry instructions external stateVar =
      { disasm := { entry, instructions, edges := (direct ++ remaining).eraseDups }
        stateVar := some var
        cases := machine.cases
        complete := machine.complete && missing.isEmpty } := by
  intro machine addresses missing assignments direct remaining
  change (match (deflatten_machine instructions stateVar).stateVar with
    | none => _
    | some _ => _) = _
  rw [h]
  rfl

theorem deflatten_recover_preserves (entry : Nat) (instructions : List Bap.Disasm.Insn) (external : List Nat)
    (stateVar : Option Bap.Var) :
    (recover entry instructions external stateVar).disasm.entry = entry ∧
      (recover entry instructions external stateVar).disasm.instructions = instructions := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none => simp [deflatten_recover_of_none hm]
  | some var => simp [deflatten_recover_of_some hm]

/-- The recovered control-flow edges contain no duplicates. -/
theorem deflatten_recover_edges_nodup (entry : Nat) (instructions : List Bap.Disasm.Insn)
    (external : List Nat) (stateVar : Option Bap.Var) :
    (recover entry instructions external stateVar).disasm.edges.Nodup := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none => simp [deflatten_recover_of_none hm]
  | some var =>
    simp only [deflatten_recover_of_some hm]
    exact callgraph_eraseDups_nodup _

/-- With no state variable the disassembly is returned with no edges and marked incomplete. -/
theorem deflatten_recover_none {instructions : List Bap.Disasm.Insn}
    (h : (Bap.Analysis.StateMachine.analyze instructions).stateVar = none) (entry : Nat)
    (external : List Nat) :
    (recover entry instructions external none).disasm.edges = [] ∧
      (recover entry instructions external none).stateVar = none ∧
      (recover entry instructions external none).cases = [] ∧
      (recover entry instructions external none).complete = false := by
  simp [deflatten_recover_of_none (stateVar := none) h]

theorem deflatten_mem_assignmentAddresses {instructions : List Bap.Disasm.Insn} {var : Bap.Var}
    {cases : List Bap.Analysis.StateMachine.Case} {address : Nat} :
    address ∈ assignmentAddresses instructions var cases ↔
      ∃ insn ∈ instructions, insn.address = address ∧
        ∃ c ∈ cases, assigns insn var c.value = true := by
  simp only [assignmentAddresses, List.mem_filterMap]
  constructor
  · rintro ⟨insn, hi, he⟩
    split at he
    · rename_i hc
      simp only [Option.some.injEq] at he
      simp only [List.any_eq_true] at hc
      exact ⟨insn, hi, he, hc⟩
    · simp at he
  · rintro ⟨insn, hi, rfl, hc⟩
    refine ⟨insn, hi, ?_⟩
    have : cases.any (fun current => assigns insn var current.value) = true := by
      simpa only [List.any_eq_true] using hc
    simp [this]

/-- `assigns` is exactly: some top-level move to the variable evaluates, closed, to the value. -/
theorem deflatten_assigns_iff {insn : Bap.Disasm.Insn} {var : Bap.Var} {value : Nat} :
    assigns insn var value = true ↔
      ∃ exp result, Bap.Bil.Stmt.move var exp ∈ insn.bil ∧ Bap.Bil.evalExp [] exp = .ok result ∧
        (Bap.Value.asBits result).toOption.any (fun bits => bits.2.toNat = value) = true := by
  simp only [assigns, List.any_eq_true]
  constructor
  · rintro ⟨stmt, hs, he⟩
    cases stmt with
    | move dst exp =>
      simp only at he
      by_cases hd : dst = var
      · subst hd
        simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at he
        split at he
        · rename_i result hr
          exact ⟨exp, result, hs, hr, he⟩
        · simp at he
      · simp [hd] at he
    | _ => simp at he
  · rintro ⟨exp, result, hs, hr, he⟩
    refine ⟨_, hs, ?_⟩
    simp [hr, he]

/-- The shape of a recovered edge: either a case edge out of an assignment of its value, or a
surviving successor edge of a non-assigning, non-indirect instruction. -/
theorem deflatten_recover_edge {entry : Nat} {instructions : List Bap.Disasm.Insn} {external : List Nat}
    {stateVar : Option Bap.Var} {source target : Nat}
    (h : (source, target) ∈ (recover entry instructions external stateVar).disasm.edges) :
    ∃ var, (recover entry instructions external stateVar).stateVar = some var ∧
      ((∃ insn ∈ instructions, insn.address = source ∧
          ∃ c ∈ (recover entry instructions external stateVar).cases,
            c.target = target ∧ assigns insn var c.value = true) ∨
        (∃ insn ∈ instructions, insn.address = source ∧ target ∈ insn.successors ∧
          insn.flow ≠ .indirectJump ∧
          source ∉ assignmentAddresses instructions var
            (recover entry instructions external stateVar).cases)) := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none =>
    rw [deflatten_recover_of_none hm] at h
    simp at h
  | some var =>
    rw [deflatten_recover_of_some hm] at h ⊢
    refine ⟨var, rfl, ?_⟩
    simp only [List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map] at h
    rcases h with ⟨c, hc, a, ha, heq⟩ | ⟨insn, hi, hr⟩
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      rcases deflatten_mem_assignmentAddresses.mp ha with ⟨insn, hi, haddr, c', hc', hass⟩
      simp only [List.mem_singleton] at hc'
      subst hc'
      exact .inl ⟨insn, hi, haddr, c', hc, rfl, hass⟩
    · split at hr
      · simp at hr
      · rename_i hcond
        simp only [List.mem_map] at hr
        rcases hr with ⟨t, ht, heq⟩
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, List.contains_iff_mem] at hcond
        exact .inr ⟨insn, hi, rfl, ht, hcond.2, hcond.1⟩

theorem deflatten_recover_edge_source {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var} {source target : Nat}
    (h : (source, target) ∈ (recover entry instructions external stateVar).disasm.edges) :
    source ∈ instructions.map Bap.Disasm.Insn.address := by
  rcases deflatten_recover_edge h with ⟨_, _, ⟨insn, hi, rfl, _⟩ | ⟨insn, hi, rfl, _⟩⟩ <;>
    exact List.mem_map_of_mem hi

/-- When recovery reports `complete`, every case target resolves inside the function or to a
declared external address. -/
theorem deflatten_recover_complete_targets {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var}
    (h : (recover entry instructions external stateVar).complete = true)
    {c : Bap.Analysis.StateMachine.Case}
    (hc : c ∈ (recover entry instructions external stateVar).cases) :
    c.target ∈ instructions.map Bap.Disasm.Insn.address ∨ c.target ∈ external := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none =>
    rw [deflatten_recover_of_none hm] at h
    simp at h
  | some var =>
    rw [deflatten_recover_of_some hm] at h hc
    simp only [Bool.and_eq_true, List.isEmpty_iff, List.filter_eq_nil_iff] at h
    have := h.2 c hc
    by_cases ha : c.target ∈ instructions.map Bap.Disasm.Insn.address
    · exact .inl ha
    · by_cases he : c.target ∈ external
      · exact .inr he
      · simp [ha, he] at this

/-- Every edge target of a `complete` recovery is resolved or is an original successor. -/
theorem deflatten_recover_complete_edge_target {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var} {source target : Nat}
    (h : (recover entry instructions external stateVar).complete = true)
    (he : (source, target) ∈ (recover entry instructions external stateVar).disasm.edges) :
    target ∈ instructions.map Bap.Disasm.Insn.address ∨ target ∈ external ∨
      ∃ insn ∈ instructions, insn.address = source ∧ target ∈ insn.successors := by
  rcases deflatten_recover_edge he with ⟨_, _, ⟨_, _, _, c, hc, rfl, _⟩ | ⟨insn, hi, hs, ht, _⟩⟩
  · rcases deflatten_recover_complete_targets h hc with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inr (.inr ⟨insn, hi, hs, ht⟩)

/-- Frame condition: an instruction that neither assigns a case value nor jumps indirectly keeps
all of its successor edges. -/
theorem deflatten_recover_keeps_successors {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var} {var : Bap.Var}
    (hvar : (recover entry instructions external stateVar).stateVar = some var)
    {insn : Bap.Disasm.Insn} (hi : insn ∈ instructions)
    (hflow : insn.flow ≠ .indirectJump)
    (hass : insn.address ∉ assignmentAddresses instructions var
      (recover entry instructions external stateVar).cases)
    {target : Nat} (ht : target ∈ insn.successors) :
    (insn.address, target) ∈ (recover entry instructions external stateVar).disasm.edges := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none =>
    rw [deflatten_recover_of_none hm] at hvar
    simp at hvar
  | some v =>
    rw [deflatten_recover_of_some hm] at hvar hass ⊢
    simp only [Option.some.injEq] at hvar
    subst hvar
    simp only [List.mem_eraseDups, List.mem_append, List.mem_flatMap]
    right
    refine ⟨insn, hi, ?_⟩
    have hc : ¬ ((assignmentAddresses instructions v
        (deflatten_machine instructions stateVar).cases).contains insn.address ||
        decide (insn.flow = .indirectJump)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem]
      exact fun h => h.elim hass hflow
    rw [ite_eq_right hc]
    exact List.mem_map_of_mem ht

/-- Assigning an instruction to a case value turns that case into an outgoing edge. -/
theorem deflatten_recover_case_edge {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var} {var : Bap.Var}
    (hvar : (recover entry instructions external stateVar).stateVar = some var)
    {insn : Bap.Disasm.Insn} (hi : insn ∈ instructions)
    {c : Bap.Analysis.StateMachine.Case} (hc : c ∈ (recover entry instructions external stateVar).cases)
    (hass : assigns insn var c.value = true) :
    (insn.address, c.target) ∈ (recover entry instructions external stateVar).disasm.edges := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none =>
    rw [deflatten_recover_of_none hm] at hvar
    simp at hvar
  | some v =>
    rw [deflatten_recover_of_some hm] at hvar hc ⊢
    simp only [Option.some.injEq] at hvar
    subst hvar
    simp only [List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_map]
    exact .inl ⟨c, hc, insn.address,
      deflatten_mem_assignmentAddresses.mpr ⟨insn, hi, rfl, c, by simp, hass⟩, rfl⟩

/-- An instruction whose address only indirect jumps occupy contributes case edges only. -/
theorem deflatten_recover_indirect_no_successor {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var} {source target : Nat}
    (he : (source, target) ∈ (recover entry instructions external stateVar).disasm.edges)
    (hindirect : ∀ insn ∈ instructions, insn.address = source → insn.flow = .indirectJump) :
    ∃ c ∈ (recover entry instructions external stateVar).cases, c.target = target := by
  rcases deflatten_recover_edge he with ⟨_, _, ⟨_, _, _, c, hc, ht, _⟩ | ⟨insn, hi, hs, _, hf, _⟩⟩
  · exact ⟨c, hc, ht⟩
  · exact absurd (hindirect insn hi hs) hf

/-- `complete` recovery implies the machine had at least two cases and no indirect jump. -/
theorem deflatten_recover_complete_two_cases {entry : Nat} {instructions : List Bap.Disasm.Insn}
    {external : List Nat} {stateVar : Option Bap.Var}
    (h : (recover entry instructions external stateVar).complete = true) :
    2 ≤ (recover entry instructions external stateVar).cases.length ∧
      ∀ insn ∈ instructions, insn.flow ≠ .indirectJump := by
  cases hm : (deflatten_machine instructions stateVar).stateVar with
  | none =>
    rw [deflatten_recover_of_none hm] at h
    simp at h
  | some var =>
    rw [deflatten_recover_of_some hm] at h ⊢
    simp only [Bool.and_eq_true] at h
    have hc := h.1
    cases stateVar with
    | some v => exact (statemachine_analyzeWithState_complete_iff _ _).mp hc
    | none => exact statemachine_analyze_complete_no_indirect hc

end Deflatten

section Signatures

open Bap.Analysis.Signatures
open_private Bap.Analysis.Signatures in Bap.Analysis.Signatures : hexByte encodeBytes decodeBytes encode decode
open_private Bap.Bil.Wire in Bap.Bil.Wire : parseHexLoop

theorem signatures_create_iff {name : String} {data mask : ByteArray} {signature : Signature} :
    create name data mask = .ok signature ↔
      data.isEmpty = false ∧ data.size = mask.size ∧ signature = ⟨name, data, mask⟩ := by
  simp only [create]
  split
  · simp_all
  · split
    · rename_i hs
      simp only [bne_iff_ne, ne_eq] at hs
      simp [hs]
    · rename_i h1 h2
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h2
      simp only [Bool.not_eq_true] at h1
      simp [h1, h2, eq_comm]

/-- `matchesAt` holds exactly when the window fits and every byte agrees under the mask. -/
theorem signatures_matchesAt_iff {signature : Signature} {data : ByteArray} {offset : Nat} :
    matchesAt signature data offset = true ↔
      offset + signature.data.size ≤ data.size ∧
        ∀ index < signature.data.size,
          data[offset + index]!.toNat &&& signature.mask[index]!.toNat =
            signature.data[index]!.toNat &&& signature.mask[index]!.toNat := by
  simp only [matchesAt]
  split
  · simp; omega
  · simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨by omega, h⟩
    · exact fun h => h.2

theorem signatures_matchesAt_out_of_range {signature : Signature} {data : ByteArray} {offset : Nat}
    (h : data.size < offset + signature.data.size) : matchesAt signature data offset = false := by
  simp [matchesAt, h]

/-- A signature always matches its own bytes, whatever the mask. -/
theorem signatures_matchesAt_self (signature : Signature) :
    matchesAt signature signature.data 0 = true := by
  simp [signatures_matchesAt_iff]

private theorem signatures_and_255 (byte : UInt8) : byte.toNat &&& 255 = byte.toNat := by
  have h : byte.toNat &&& (2 ^ 8 - 1) = byte.toNat % 2 ^ 8 := Nat.and_two_pow_sub_one_eq_mod _ _
  have hb := byte.toNat_lt
  simp only [Nat.reducePow, Nat.add_one_sub_one] at h
  rw [h]
  exact Nat.mod_eq_of_lt (by simpa using hb)

/-- With an all-ones mask matching is exact byte comparison. -/
theorem signatures_matchesAt_full_mask {signature : Signature} {data : ByteArray} {offset : Nat}
    (hmask : ∀ index < signature.data.size, signature.mask[index]!.toNat = 255) :
    matchesAt signature data offset = true ↔
      offset + signature.data.size ≤ data.size ∧
        ∀ index < signature.data.size, data[offset + index]! = signature.data[index]! := by
  rw [signatures_matchesAt_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro index
  apply imp_congr_right
  intro hi
  rw [hmask index hi, signatures_and_255, signatures_and_255]
  exact UInt8.toNat_inj

/-- With a zero mask every in-range offset matches. -/
theorem signatures_matchesAt_zero_mask {signature : Signature} {data : ByteArray} {offset : Nat}
    (hmask : ∀ index < signature.data.size, signature.mask[index]!.toNat = 0) :
    matchesAt signature data offset = true ↔ offset + signature.data.size ≤ data.size := by
  rw [signatures_matchesAt_iff]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun index hi => ?_⟩
    simp [hmask index hi]

/-- Clearing mask bits can only add matches. -/
theorem signatures_matchesAt_mask_mono {name : String} {pattern mask narrower data : ByteArray} {offset : Nat}
    (hsub : ∀ index < pattern.size, narrower[index]!.toNat &&& mask[index]!.toNat = narrower[index]!.toNat)
    (h : matchesAt ⟨name, pattern, mask⟩ data offset = true) :
    matchesAt ⟨name, pattern, narrower⟩ data offset = true := by
  rw [signatures_matchesAt_iff] at h ⊢
  refine ⟨h.1, fun index hi => ?_⟩
  have he := h.2 index hi
  simp only at he hi ⊢
  rw [← hsub index hi, ← Nat.and_assoc, ← Nat.and_assoc, Nat.and_comm _ (narrower[index]!.toNat),
    Nat.and_comm _ (narrower[index]!.toNat), Nat.and_assoc, Nat.and_assoc, he]

/-- `find` returns exactly the addresses of matching offsets, over all regions. -/
theorem signatures_mem_find {image : Bap.Image.Image} {signature : Signature} {address : Nat} :
    address ∈ find image signature ↔
      ∃ entry ∈ image.memory.entries, ∃ offset,
        matchesAt signature entry.1.data offset = true ∧ address = entry.1.addr + offset := by
  simp only [find, List.mem_flatMap]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _
  constructor
  · intro h
    split at h
    · simp at h
    · simp only [List.mem_filterMap, List.mem_range] at h
      rcases h with ⟨offset, _, he⟩
      split at he
      · rename_i hm
        simp only [Option.some.injEq] at he
        exact ⟨offset, hm, he.symm⟩
      · simp at he
  · rintro ⟨offset, hm, rfl⟩
    have hfit := (signatures_matchesAt_iff.mp hm).1
    rw [ite_eq_right (by omega)]
    simp only [List.mem_filterMap, List.mem_range]
    exact ⟨offset, by omega, by simp [hm]⟩


private theorem signatures_toList_loop (bs : ByteArray) (k i : Nat) (r : List UInt8)
    (h : bs.size - i = k) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction k generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop]
    have hs : bs.data.size = bs.size := rfl
    rw [ite_eq_right (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | succ k ih =>
    rw [ByteArray.toList.loop]
    have hs : bs.data.size = bs.size := rfl
    have hi : i < bs.size := by omega
    rw [ite_eq_left hi, ih (i + 1) _ (by omega)]
    have hd : bs.data.toList.drop i = bs.get! i :: bs.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      congr 1
      cases bs with
      | mk data =>
        simp only [ByteArray.get!]
        simp [getElem!_pos, show i < data.size from hi]
    rw [hd]
    simp

theorem signatures_byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have := signatures_toList_loop bs _ 0 [] rfl
  simpa [ByteArray.toList] using this

private def signatures_hexChars (n : Nat) : List Char :=
  (if (Nat.toDigits 16 n).length < 2 then ['0'] else []) ++ Nat.toDigits 16 n

private def signatures_hexOk (n : Nat) : Bool :=
  match parseHexLoop (signatures_hexChars n) 0 with
  | .ok value => value == n && !(signatures_hexChars n).isEmpty
  | .error _ => false

private theorem signatures_hexOk_all : ∀ n, n < 256 → signatures_hexOk n = true := by
  decide +kernel

theorem signatures_parseHex_hexByte (byte : UInt8) :
    Bap.Bil.Wire.parseHex (hexByte byte) = .ok byte.toNat := by
  have hlt : byte.toNat < 256 := by simpa using byte.toNat_lt
  have hc := signatures_hexOk_all _ hlt
  have hs : (hexByte byte).toList = signatures_hexChars byte.toNat := by
    simp only [hexByte, signatures_hexChars]
    split <;> rename_i h <;> simp only [String.length_ofList] at h <;> simp [h]
  have hne : (hexByte byte).isEmpty = false := by
    have hl : (hexByte byte).toList ≠ [] := by
      rw [hs]
      simp only [signatures_hexOk] at hc
      split at hc
      · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
        exact hc.2
      · simp at hc
    cases he : (hexByte byte).isEmpty with
    | false => rfl
    | true =>
      have : hexByte byte = "" := by simpa [String.isEmpty_iff] using he
      simp [this] at hl
  simp only [Bap.Bil.Wire.parseHex, hne, hs, Bool.false_eq_true, ite_false]
  simp only [signatures_hexOk] at hc
  split at hc
  · rename_i value hv
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rw [hv, hc.1]
  · simp at hc

private theorem signatures_mapM_decode (bytes : List UInt8) :
    (bytes.map fun byte => Bap.Sexp.atom (hexByte byte)).mapM (m := Except String) (fun atom => do
      let atom ← Bap.Sexp.asAtom atom
      Bap.Bil.Wire.parseHex atom) = .ok (bytes.map UInt8.toNat) := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih]
    simp only [Bap.Sexp.asAtom, bind, Except.bind, signatures_parseHex_hexByte]
    rfl

/-- The byte-list encoding round-trips for every byte array. -/
theorem signatures_decodeBytes_encodeBytes (data : ByteArray) :
    decodeBytes (encodeBytes data) = .ok data := by
  simp only [decodeBytes, encodeBytes, signatures_byteArray_toList, Bap.Sexp.asList]
  change (do
    let values ← (data.data.toList.map fun byte => Bap.Sexp.atom (hexByte byte)).mapM
      (m := Except String) (fun atom => do
        let atom ← Bap.Sexp.asAtom atom
        Bap.Bil.Wire.parseHex atom)
    if values.any (fun value => decide (value ≥ 256)) = true then
      Except.error "signature byte is out of range"
    else
      Except.ok (ByteArray.mk (values.map UInt8.ofNat).toArray)) = _
  rw [signatures_mapM_decode]
  have hany : (data.data.toList.map UInt8.toNat).any (fun value => decide (value ≥ 256)) = false := by
    simp only [List.any_eq_false, List.mem_map, decide_eq_true_eq]
    rintro _ ⟨byte, _, rfl⟩
    have := byte.toNat_lt
    simp at this
    omega
  simp only [bind, Except.bind, hany, Bool.false_eq_true, ite_false, List.map_map]
  have hid : (UInt8.ofNat ∘ UInt8.toNat) = id := by
    funext byte
    simp
  rw [hid]
  simp

/-- A well-formed signature (one `create` accepts) survives the wire format. -/
theorem signatures_decode_encode {name : String} {data mask : ByteArray} {signature : Signature}
    (h : create name data mask = .ok signature) : decode (encode signature) = .ok signature := by
  rcases signatures_create_iff.mp h with ⟨_, _, rfl⟩
  simp only [encode, decode, Bap.Sexp.tagged, Bap.Sexp.expectTagged, Bap.Sexp.asList, Bap.Sexp.asAtom]
  simp [bind, Except.bind, signatures_decodeBytes_encodeBytes, h]

end Signatures

section Protobuf

open Bap.Analysis.Protobuf
open_private Bap.Analysis.Protobuf in Bap.Analysis.Protobuf : varint varint.loop

private theorem protobuf_loop_unfold (data : ByteArray) (shift offset value : Nat) :
    varint.loop data shift offset value =
      if shift > 63 then .error "oversized protobuf varint"
      else if offset ≥ data.size then .error "truncated protobuf varint"
      else if value + (data[offset]!.toNat % 128) * 2 ^ shift ≥ 2 ^ 64 then
        .error "protobuf varint exceeds 64 bits"
      else if data[offset]!.toNat < 128 then
        .ok (value + (data[offset]!.toNat % 128) * 2 ^ shift, offset + 1)
      else varint.loop data (shift + 7) (offset + 1) (value + (data[offset]!.toNat % 128) * 2 ^ shift) := by
  rw [varint.loop]

theorem protobuf_varint_eq (data : ByteArray) (offset : Nat) :
    varint data offset = varint.loop data 0 offset 0 := rfl

private theorem protobuf_loop_bounds (data : ByteArray) (k shift offset value : Nat) (hk : 64 - shift ≤ k)
    {result next : Nat} (h : varint.loop data shift offset value = .ok (result, next)) :
    offset < next ∧ next ≤ data.size ∧ next * 7 + shift ≤ offset * 7 + 70 ∧ result < 2 ^ 64 := by
  induction k generalizing shift offset value with
  | zero =>
    rw [protobuf_loop_unfold] at h
    rw [ite_eq_left (by omega)] at h
    cases h
  | succ k ih =>
    rw [protobuf_loop_unfold] at h
    by_cases h1 : shift > 63
    · rw [ite_eq_left h1] at h
      cases h
    rw [ite_eq_right h1] at h
    by_cases h2 : offset ≥ data.size
    · rw [ite_eq_left h2] at h
      cases h
    rw [ite_eq_right h2] at h
    by_cases h3 : value + (data[offset]!.toNat % 128) * 2 ^ shift ≥ 2 ^ 64
    · rw [ite_eq_left h3] at h
      cases h
    rw [ite_eq_right h3] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by omega, by omega, by omega, Nat.lt_of_not_ge h3⟩
    · have := ih (shift + 7) (offset + 1) _ (by omega) h
      exact ⟨by omega, this.2.1, by omega, this.2.2.2⟩

/-- A successful varint decode advances, stays in bounds, reads at most ten bytes, and yields a
value that fits in 64 bits, the range of the protobuf wire format. -/
theorem protobuf_varint_bounds {data : ByteArray} {offset result next : Nat}
    (h : varint data offset = .ok (result, next)) :
    offset < next ∧ next ≤ data.size ∧ next ≤ offset + 10 ∧ result < 2 ^ 64 := by
  have := protobuf_loop_bounds data 64 0 offset 0 (by omega) h
  exact ⟨this.1, this.2.1, by omega, this.2.2.2⟩

theorem protobuf_varint_one_byte {data : ByteArray} {offset : Nat} (hin : offset < data.size)
    (h : data[offset]!.toNat < 128) : varint data offset = .ok (data[offset]!.toNat, offset + 1) := by
  have hsmall : ¬ (0 + (data[offset]!.toNat % 128) * 2 ^ 0 ≥ 2 ^ 64) := by
    simp only [Nat.reducePow]
    omega
  rw [protobuf_varint_eq, protobuf_loop_unfold]
  rw [ite_eq_right (by decide), ite_eq_right (by omega), ite_eq_right hsmall, ite_eq_left h]
  simp
  omega

theorem protobuf_varint_truncated {data : ByteArray} {offset : Nat} (h : data.size ≤ offset) :
    varint data offset = .error "truncated protobuf varint" := by
  rw [protobuf_varint_eq, protobuf_loop_unfold]
  rw [ite_eq_right (by decide), ite_eq_left h]

private theorem protobuf_loop_error (data : ByteArray) (k shift offset value : Nat) (hk : 64 - shift ≤ k)
    {message : String} (h : varint.loop data shift offset value = .error message) :
    message = "oversized protobuf varint" ∨ message = "truncated protobuf varint" ∨
      message = "protobuf varint exceeds 64 bits" := by
  induction k generalizing shift offset value with
  | zero =>
    rw [protobuf_loop_unfold, ite_eq_left (by omega)] at h
    cases h
    exact .inl rfl
  | succ k ih =>
    rw [protobuf_loop_unfold] at h
    split at h
    · cases h
      exact .inl rfl
    · split at h
      · cases h
        exact .inr (.inl rfl)
      · split at h
        · cases h
          exact .inr (.inr rfl)
        · split at h
          · cases h
          · exact ih (shift + 7) (offset + 1) _ (by omega) h

theorem protobuf_varint_error {data : ByteArray} {offset : Nat} {message : String}
    (h : varint data offset = .error message) :
    message = "oversized protobuf varint" ∨ message = "truncated protobuf varint" ∨
      message = "protobuf varint exceeds 64 bits" :=
  protobuf_loop_error data 64 0 offset 0 (by omega) h

/-- A reference little-endian base-128 encoder, used to specify `varint`. -/
def protobuf_encodeVarint : Nat → Nat → List Nat
  | 0, value => [value]
  | fuel + 1, value =>
    if value < 128 then [value] else (value % 128 + 128) :: protobuf_encodeVarint fuel (value / 128)

private theorem protobuf_loop_encoded (data : ByteArray) (k : Nat) :
    ∀ (shift offset accumulated value : Nat), value < 2 ^ (7 * (k + 1)) → shift + 7 * k ≤ 63 →
      accumulated + value * 2 ^ shift < 2 ^ 64 →
      offset + (protobuf_encodeVarint k value).length ≤ data.size →
      (∀ index (hi : index < (protobuf_encodeVarint k value).length),
        data[offset + index]!.toNat = (protobuf_encodeVarint k value)[index]) →
      varint.loop data shift offset accumulated =
        .ok (accumulated + value * 2 ^ shift, offset + (protobuf_encodeVarint k value).length) := by
  induction k with
  | zero =>
    intro shift offset accumulated value hv hs hfit hsize hbytes
    simp only [protobuf_encodeVarint, List.length_singleton] at hsize hbytes ⊢
    have hb := hbytes 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hb
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reducePow] at hv hs
    rw [protobuf_loop_unfold, ite_eq_right (by omega), ite_eq_right (by omega), hb,
      Nat.mod_eq_of_lt hv, ite_eq_right (Nat.not_le.mpr hfit), ite_eq_left hv]
  | succ k ih =>
    intro shift offset accumulated value hv hs hfit hsize hbytes
    rw [protobuf_loop_unfold, ite_eq_right (by omega)]
    by_cases hsmall : value < 128
    · have hen : protobuf_encodeVarint (k + 1) value = [value] := by
        simp [protobuf_encodeVarint, hsmall]
      rw [hen] at hsize hbytes ⊢
      simp only [List.length_singleton] at hsize ⊢
      have hb := hbytes 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hb
      rw [ite_eq_right (by omega), hb, Nat.mod_eq_of_lt hsmall, ite_eq_right (Nat.not_le.mpr hfit),
        ite_eq_left hsmall]
    · have hen : protobuf_encodeVarint (k + 1) value =
          (value % 128 + 128) :: protobuf_encodeVarint k (value / 128) := by
        simp [protobuf_encodeVarint, hsmall]
      rw [hen] at hsize hbytes ⊢
      simp only [List.length_cons] at hsize ⊢
      have hb := hbytes 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hb
      have hmod : value % 128 < 128 := Nat.mod_lt _ (by decide)
      have hge : ¬ (value % 128 + 128 < 128) := by omega
      have hm2 : (value % 128 + 128) % 128 = value % 128 := by omega
      have hsum : accumulated + value % 128 * 2 ^ shift + value / 128 * 2 ^ (shift + 7) =
          accumulated + value * 2 ^ shift := by
        have hd : value = value % 128 + 128 * (value / 128) := (Nat.mod_add_div _ _).symm
        conv => rhs; rw [hd]
        rw [Nat.pow_add, Nat.add_mul, Nat.add_assoc]
        simp only [Nat.reducePow]
        congr 2
        rw [Nat.mul_assoc, Nat.mul_comm 128, Nat.mul_comm (value / 128), Nat.mul_assoc, Nat.mul_comm (2 ^ shift)]
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have hpartial : ¬ (accumulated + value % 128 * 2 ^ shift ≥ 2 ^ 64) := by omega
      rw [ite_eq_right (by omega), hb, hm2, ite_eq_right hpartial, ite_eq_right hge]
      have hq : value / 128 < 2 ^ (7 * (k + 1)) := by
        apply Nat.div_lt_of_lt_mul
        have he : 7 * (k + 1 + 1) = 7 + 7 * (k + 1) := by omega
        rw [he, Nat.pow_add] at hv
        exact hv
      have hrec := ih (shift + 7) (offset + 1) (accumulated + value % 128 * 2 ^ shift) (value / 128) hq
        (by omega) (by omega) (by omega) (by
          intro index hi
          have := hbytes (index + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at this
          rw [← this]
          congr 2
          omega)
      rw [hrec, hsum]
      congr 2
      omega

/-- Roundtrip: whenever `data` holds the reference encoding of a 64-bit value at `offset`, `varint`
decodes that value and stops right after the encoding. -/
theorem protobuf_varint_encoded {data : ByteArray} {offset value : Nat} (hv : value < 2 ^ 64)
    (hsize : offset + (protobuf_encodeVarint 9 value).length ≤ data.size)
    (hbytes : ∀ index (hi : index < (protobuf_encodeVarint 9 value).length),
      data[offset + index]!.toNat = (protobuf_encodeVarint 9 value)[index]) :
    varint data offset = .ok (value, offset + (protobuf_encodeVarint 9 value).length) := by
  have := protobuf_loop_encoded data 9 0 offset 0 value
    (Nat.lt_of_lt_of_le hv (by decide)) (by decide) (by simpa using hv) hsize hbytes
  simpa [protobuf_varint_eq] using this

/-- Any value a tenth byte carries past bit 0 is rejected: at shift 63, a payload of 2 or more
cannot fit in 64 bits. -/
theorem protobuf_loop_tenth_byte_rejected {data : ByteArray} {offset : Nat} (value : Nat)
    (hin : offset < data.size) (hbyte : 2 ≤ data[offset]!.toNat % 128) :
    varint.loop data 63 offset value = .error "protobuf varint exceeds 64 bits" := by
  have hlarge : value + (data[offset]!.toNat % 128) * 2 ^ 63 ≥ 2 ^ 64 := by
    have : 2 * 2 ^ 63 ≤ (data[offset]!.toNat % 128) * 2 ^ 63 := Nat.mul_le_mul_right _ hbyte
    simp only [Nat.reducePow] at this ⊢
    omega
  rw [protobuf_loop_unfold, ite_eq_right (by decide), ite_eq_right (by omega), ite_eq_left hlarge]

private theorem protobuf_loop_continue {data : ByteArray} {shift offset value byte : Nat} (hs : shift ≤ 63)
    (hin : offset < data.size) (hb : data[offset]!.toNat = byte) (hc : 128 ≤ byte)
    (hfit : value + byte % 128 * 2 ^ shift < 2 ^ 64) :
    varint.loop data shift offset value =
      varint.loop data (shift + 7) (offset + 1) (value + byte % 128 * 2 ^ shift) := by
  subst hb
  rw [protobuf_loop_unfold, ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (Nat.not_le.mpr hfit), ite_eq_right (by omega)]

private def protobuf_overlong : ByteArray := ByteArray.mk #[255, 255, 255, 255, 255, 255, 255, 255, 255, 127]

/-- Regression: the ten-byte encoding of `2^70 - 1` is an error, while the largest 64-bit value
still decodes. -/
theorem protobuf_varint_rejects_over_64_bits :
    varint protobuf_overlong 0 = .error "protobuf varint exceeds 64 bits" := by
  have hsize : protobuf_overlong.size = 10 := rfl
  have step (shift offset value : Nat) (hs : shift ≤ 63) (hin : offset < 9)
      (hb : protobuf_overlong[offset]!.toNat = 255)
      (hfit : value + 255 % 128 * 2 ^ shift < 2 ^ 64) :
      varint.loop protobuf_overlong shift offset value =
        varint.loop protobuf_overlong (shift + 7) (offset + 1) (value + 255 % 128 * 2 ^ shift) :=
    protobuf_loop_continue hs (by omega) hb (by decide) hfit
  rw [protobuf_varint_eq]
  refine (step 0 0 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 7 1 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 14 2 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 21 3 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 28 4 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 35 5 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 42 6 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 49 7 _ (by decide) (by decide) rfl (by decide)).trans ?_
  refine (step 56 8 _ (by decide) (by decide) rfl (by decide)).trans ?_
  exact protobuf_loop_tenth_byte_rejected _ (by rw [hsize]; decide) (by decide)

theorem protobuf_varint_max_64_bits :
    varint (ByteArray.mk #[255, 255, 255, 255, 255, 255, 255, 255, 255, 1]) 0 = .ok (2 ^ 64 - 1, 10) := by
  have hv : (2 : Nat) ^ 64 - 1 < 2 ^ 64 := by decide
  have he : protobuf_encodeVarint 9 (2 ^ 64 - 1) = [255, 255, 255, 255, 255, 255, 255, 255, 255, 1] := by
    decide
  have := protobuf_varint_encoded (data := ByteArray.mk #[255, 255, 255, 255, 255, 255, 255, 255, 255, 1])
    (offset := 0) hv (by rw [he]; decide) (by
      rw [he]
      intro index hi
      simp only [List.length_cons, List.length_nil] at hi
      rcases index with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | index
      all_goals first | rfl | omega)
  rw [he] at this
  exact this

private theorem protobuf_varint_message_ne {data : ByteArray} {offset : Nat}
    (h : varint data offset = .error "too many protobuf fields") : False := by
  rcases protobuf_varint_error h with h | h | h <;> revert h <;> decide

/-- A field `fields` may return: a nonzero number, a supported wire type, and a payload whose shape
agrees with the wire type. -/
def protobuf_wellFormed (data : ByteArray) (field : Field) : Prop :=
  field.number ≠ 0 ∧
    ((field.wire = 0 ∧ ∃ value, field.value = .varint value) ∨
      (field.wire = 1 ∧ ∃ bytes, field.value = .bytes bytes ∧ bytes.size = 8) ∨
      (field.wire = 2 ∧ ∃ bytes, field.value = .bytes bytes ∧ bytes.size ≤ data.size) ∨
      (field.wire = 5 ∧ ∃ bytes, field.value = .bytes bytes ∧ bytes.size = 4))

/-- One iteration of the `fields` loop, with fuel available and input remaining: either an error or
a well-formed field and a strictly larger offset. -/
private theorem protobuf_loop_step {data : ByteArray} {fuel offset : Nat} {result : List Field}
    (hin : ¬ offset ≥ data.size) {final : Except String (List Field)}
    (h : fields.loop data (fuel + 1) offset result = final) :
    (∃ message, final = .error message ∧ message ≠ "too many protobuf fields") ∨
      ∃ field next, protobuf_wellFormed data field ∧ offset < next ∧ next ≤ data.size ∧
        final = fields.loop data fuel next (field :: result) := by
  rw [fields.loop] at h
  subst h
  rw [ite_eq_right hin]
  simp only [bind, Except.bind]
  cases htag : varint data offset with
  | error message =>
    refine .inl ⟨message, rfl, ?_⟩
    intro he
    subst he
    exact protobuf_varint_message_ne htag
  | ok tag =>
    rcases tag with ⟨tag, offset1⟩
    have hb1 := protobuf_varint_bounds htag
    simp only
    by_cases hn : tag / 8 = 0
    · rw [ite_eq_left hn]
      exact .inl ⟨_, rfl, by decide⟩
    rw [ite_eq_right hn]
    have hwire : tag % 8 < 8 := Nat.mod_lt _ (by decide)
    generalize hw : tag % 8 = wire at hwire ⊢
    match wire, hwire, hw with
    | 0, _, hw =>
      simp only
      cases hval : varint data offset1 with
      | error message =>
        refine .inl ⟨message, rfl, ?_⟩
        intro he
        subst he
        exact protobuf_varint_message_ne hval
      | ok value =>
        rcases value with ⟨value, offset2⟩
        have hb2 := protobuf_varint_bounds hval
        exact .inr ⟨⟨tag / 8, 0, .varint value⟩, offset2,
          ⟨hn, .inl ⟨rfl, value, rfl⟩⟩, by omega, hb2.2.1, rfl⟩
    | 1, _, hw =>
      simp only
      split
      · exact .inl ⟨_, rfl, by decide⟩
      · rename_i hfit
        refine .inr ⟨⟨tag / 8, 1, .bytes (data.extract offset1 (offset1 + 8))⟩, offset1 + 8,
          ⟨hn, .inr (.inl ⟨rfl, _, rfl, ?_⟩)⟩, by omega, by omega, rfl⟩
        simp [ByteArray.size_extract]
        omega
    | 2, _, hw =>
      simp only
      cases hval : varint data offset1 with
      | error message =>
        refine .inl ⟨message, rfl, ?_⟩
        intro he
        subst he
        exact protobuf_varint_message_ne hval
      | ok value =>
        rcases value with ⟨size, offset2⟩
        have hb2 := protobuf_varint_bounds hval
        simp only
        split
        · exact .inl ⟨_, rfl, by decide⟩
        · rename_i hfit
          refine .inr ⟨⟨tag / 8, 2, .bytes (data.extract offset2 (offset2 + size))⟩, offset2 + size,
            ⟨hn, .inr (.inr (.inl ⟨rfl, _, rfl, ?_⟩))⟩, by omega, by omega, rfl⟩
          simp [ByteArray.size_extract]
          omega
    | 5, _, hw =>
      simp only
      split
      · exact .inl ⟨_, rfl, by decide⟩
      · rename_i hfit
        refine .inr ⟨⟨tag / 8, 5, .bytes (data.extract offset1 (offset1 + 4))⟩, offset1 + 4,
          ⟨hn, .inr (.inr (.inr ⟨rfl, _, rfl, ?_⟩))⟩, by omega, by omega, rfl⟩
        simp [ByteArray.size_extract]
        omega
    | 3, _, hw => exact .inl ⟨_, rfl, by decide +kernel⟩
    | 4, _, hw => exact .inl ⟨_, rfl, by decide +kernel⟩
    | 6, _, hw => exact .inl ⟨_, rfl, by decide +kernel⟩
    | 7, _, hw => exact .inl ⟨_, rfl, by decide +kernel⟩

/-- Every step advances the offset, so a budget above the bytes remaining never runs out. -/
theorem protobuf_loop_fuel_sufficient (data : ByteArray) (fuel offset : Nat) (result : List Field)
    (hfuel : data.size - offset < fuel) :
    fields.loop data fuel offset result ≠ .error "too many protobuf fields" := by
  induction fuel generalizing offset result with
  | zero => omega
  | succ fuel ih =>
    by_cases hin : offset ≥ data.size
    · rw [fields.loop, ite_eq_left hin]
      simp
    · rcases protobuf_loop_step hin rfl with ⟨message, he, hne⟩ | ⟨field, next, _, hlt, _, he⟩
      · rw [he]
        intro h
        cases h
        exact hne rfl
      · rw [he]
        exact ih next _ (by omega)

/-- `fields` never reports exhausting its budget: the fuel is only a termination device. -/
theorem protobuf_fields_never_exhausted (data : ByteArray) :
    fields data ≠ .error "too many protobuf fields" :=
  protobuf_loop_fuel_sufficient data _ 0 [] (by omega)

/-- More fuel than bytes remaining makes the result independent of the exact budget. -/
theorem protobuf_loop_fuel_irrelevant (data : ByteArray) (fuel extra offset : Nat) (result : List Field)
    (hfuel : data.size - offset < fuel) :
    fields.loop data (fuel + extra) offset result = fields.loop data fuel offset result := by
  induction fuel generalizing offset result with
  | zero => omega
  | succ fuel ih =>
    rw [show fuel + 1 + extra = fuel + extra + 1 by omega]
    by_cases hin : offset ≥ data.size
    · rw [fields.loop, ite_eq_left hin, fields.loop, ite_eq_left hin]
    · rw [fields.loop, ite_eq_right hin, fields.loop.eq_2, ite_eq_right hin]
      simp only [bind, Except.bind]
      cases htag : varint data offset with
      | error message => rfl
      | ok tag =>
        rcases tag with ⟨tag, offset1⟩
        have hb1 := protobuf_varint_bounds htag
        simp only
        split
        · rfl
        · split
          · cases hval : varint data offset1 with
            | error message => rfl
            | ok value =>
              have hb2 := protobuf_varint_bounds hval
              exact ih _ _ (by omega)
          · split
            · rfl
            · exact ih _ _ (by omega)
          · cases hval : varint data offset1 with
            | error message => rfl
            | ok value =>
              have hb2 := protobuf_varint_bounds hval
              simp only
              split
              · rfl
              · exact ih _ _ (by omega)
          · split
            · rfl
            · exact ih _ _ (by omega)
          · rfl

private theorem protobuf_loop_wellFormed (data : ByteArray) (fuel offset : Nat) (result output : List Field)
    (hresult : ∀ field ∈ result, protobuf_wellFormed data field)
    (h : fields.loop data fuel offset result = .ok output) :
    ∀ field ∈ output, protobuf_wellFormed data field := by
  induction fuel generalizing offset result with
  | zero =>
    rw [fields.loop] at h
    cases h
  | succ fuel ih =>
    by_cases hin : offset ≥ data.size
    · rw [fields.loop, ite_eq_left hin] at h
      simp only [Except.ok.injEq] at h
      subst h
      simpa using hresult
    · rcases protobuf_loop_step hin rfl with ⟨message, he, _⟩ | ⟨field, next, hw, _, _, he⟩
      · rw [he] at h
        cases h
      · rw [he] at h
        apply ih next _ _ h
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hw
        · exact hresult f hf

/-- Each decoded field has a nonzero number, a supported wire type and a matching payload. -/
theorem protobuf_fields_wellFormed {data : ByteArray} {output : List Field}
    (h : fields data = .ok output) : ∀ field ∈ output, protobuf_wellFormed data field :=
  protobuf_loop_wellFormed data _ 0 [] output (by simp) h

theorem protobuf_fields_empty {data : ByteArray} (h : data.size = 0) : fields data = .ok [] := by
  simp only [fields]
  rw [fields.loop, ite_eq_left (by omega)]
  rfl

/-- Decoding emits at most one field per input byte. -/
theorem protobuf_fields_length_le {data : ByteArray} {output : List Field}
    (h : fields data = .ok output) : output.length ≤ data.size := by
  have aux : ∀ (fuel offset : Nat) (result output : List Field), offset ≤ data.size →
      fields.loop data fuel offset result = .ok output →
      output.length + offset ≤ result.length + data.size := by
    intro fuel
    induction fuel with
    | zero =>
      intro offset result output _ h
      rw [fields.loop] at h
      cases h
    | succ fuel ih =>
      intro offset result output ho h
      by_cases hin : offset ≥ data.size
      · rw [fields.loop, ite_eq_left hin] at h
        simp only [Except.ok.injEq] at h
        subst h
        simp
        omega
      · rcases protobuf_loop_step hin rfl with ⟨message, he, _⟩ | ⟨field, next, _, hlt, hle, he⟩
        · rw [he] at h
          cases h
        · rw [he] at h
          have := ih next _ _ hle h
          simp only [List.length_cons] at this
          omega
  have := aux _ 0 [] output (by omega) h
  simpa using this

/-- A validated blob has exactly the two non-empty byte fields, and the payload re-decodes to the
reported non-empty inner fields. -/
theorem protobuf_validateSignedPbiData_sound {data : ByteArray} {result : SignedPbiData}
    (h : validateSignedPbiData data = .ok result) :
    result.payload.size ≠ 0 ∧ result.signature.size ≠ 0 ∧
      fields result.payload = .ok result.unsignedFields ∧ result.unsignedFields ≠ [] ∧
      fields data = .ok [⟨1, 2, .bytes result.payload⟩, ⟨2, 2, .bytes result.signature⟩] := by
  simp only [validateSignedPbiData, bind, Except.bind] at h
  cases htop : fields data with
  | error message =>
    rw [htop] at h
    cases h
  | ok top =>
    rw [htop] at h
    simp only at h
    match top, h with
    | [⟨n1, w1, v1⟩, ⟨n2, w2, v2⟩], h =>
      simp only at h
      split at h
      · cases h
      · rename_i hcheck
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hcheck
        rcases hcheck with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
        cases v1 with
        | varint value => cases h
        | bytes payload =>
          cases v2 with
          | varint value => cases h
          | bytes signature =>
            simp only at h
            split at h
            · cases h
            · rename_i hne
              simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hne
              cases hin : fields payload with
              | error message =>
                rw [hin] at h
                cases h
              | ok inner =>
                rw [hin] at h
                simp only at h
                split at h
                · cases h
                · rename_i hempty
                  simp only [Except.ok.injEq] at h
                  subst h
                  refine ⟨hne.1, hne.2, hin, ?_, rfl⟩
                  simpa using hempty
    | [], h => cases h
    | [_], h => cases h
    | _ :: _ :: _ :: _, h => cases h

end Protobuf

end Bap.Proofs.Analysis
