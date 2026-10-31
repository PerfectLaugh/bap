import Lean
import Bap.Proofs.Primus

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

/-! A whole load of definitions, and the environments whose instructions are compiled when they are first looked at. -/

namespace Bap.Proofs.Primus

open Bap.Primus.Semantics
open_private Bap.Primus.Semantics Bap.Primus.Semantics evalTopLevel evalFormsIn topLevelState define addDefinition compileValue compileCallable apply

/-! ### A load -/

private theorem foldl_indexed {context : Context} {state after : State} {forms : List Sexp} (h : Indexed state)
    (he : forms.foldlM (evalTopLevel context) state = .ok after) : Indexed after := by
  induction forms generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at he
    exact he ▸ h
  | cons form rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at he
    cases hf : evalTopLevel context state form with
    | error e =>
      rw [hf] at he
      cases he
    | ok mid =>
      rw [hf] at he
      exact ih (evalTopLevel_indexed h hf) he

/-- **The tables stay right through a whole load**, whichever forms it has and however it starts, as long as they were right. -/
theorem evalFormsIn_indexed {context : Context} {state after : State} {forms : List Sexp} (h : Indexed state)
    (he : evalFormsIn context state forms = .ok after) : Indexed after := by
  simp only [evalFormsIn, bind, Except.bind] at he
  split at he
  · cases he
  · exact foldl_indexed h he

/-- And they are right from the start. -/
theorem evalForms_indexed {context : Context} {globals : Globals} {forms : List Sexp} {after : State}
    (he : evalForms context globals forms = .ok after) : Indexed after :=
  evalFormsIn_indexed (topLevelState_indexed globals) he

/-- So that `define` is what `define_spec` says after a whole load. -/
theorem evalForms_define_spec {context : Context} {globals : Globals} {forms : List Sexp} {after : State}
    (he : evalForms context globals forms = .ok after) (name : String) (callable : Callable) :
    define after name callable =
      { after with
        globals := Assoc.put name (.callable (addDefinition callable (Assoc.get name after.globals))) after.globals
        operations := after.operations.insert name (addDefinition callable (Assoc.get name after.globals))
        defined := after.defined.insert name } :=
  define_spec (evalForms_indexed he) name callable

/-! ### Thunked environments

`compilePartly` puts off the compilation of `lazy`. `Compat` is about what a name finds up to compilation, so that it holds of the state of the
thunked environment that `compiledDefinitions` builds as it does of the one with all compiled (`thunked_compat`). So each instruction that environment
lifts, which is a thunk that compiles it, has the same successes as the instruction as it was written (`thunked_opcode_agrees`, `thunked_instruction_agrees`). -/

/-- All of the definitions of a target, as `compiledDefinitions` puts them. -/
def allOf (eager : Globals) (lazy : List (String × Callable)) : Globals :=
  eager ++ lazy.map fun binding => (binding.1, .callable binding.2)

/-- **Forcing every thunk gives what `compileGlobals` gives**: a thunk holds the compilation of its instruction against all of the definitions, as `lift` would have it. -/
theorem compilePartly_forced (eager : Globals) (lazy : List (String × Callable)) :
    (compilePartly eager lazy (globalsTable (allOf eager lazy))).1 ++
        (compilePartly eager lazy (globalsTable (allOf eager lazy))).2.map (fun binding => (binding.1, Value.callable binding.2.get)) =
      compileGlobals (allOf eager lazy) := by
  simp [compilePartly, compileGlobals, allOf, compileValue, Thunk.get]

/-- What a lazy environment forces to is a state that compiled code agrees with the interpreter in. -/
theorem forced_compat (eager : Globals) (lazy : List (String × Callable)) :
    Compat (allOf eager lazy) (liftState (allOf eager lazy)) :=
  compat_ofGlobals _

/-- A thunk is the compilation of its instruction against all of the definitions, whichever of them were forced. -/
theorem compilePartly_thunk (eager : Globals) (lazy : List (String × Callable)) (table : Std.HashMap String Bap.Primus.Semantics.Value) {name : String} {thunk : Thunk Callable}
    (h : (name, thunk) ∈ (compilePartly eager lazy table).2) :
    ∃ callable, (name, callable) ∈ lazy ∧ thunk.get = compileCallable (fun name => table.get? name) callable := by
  simp only [compilePartly, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨⟨key, callable⟩, hm, h1, h2⟩ := h
  subst h1
  subst h2
  exact ⟨callable, hm, rfl⟩

/-- In a thunked environment a name that is not an instruction finds what it finds in the compiled definitions, as in `lift`: the state differs from that of `Compat` at the instructions alone. -/
theorem compilePartly_lookup (eager : Globals) (lazy : List (String × Callable)) {name : String} (hn : ∀ binding ∈ lazy, binding.1 ≠ name) :
    Assoc.get name ((compilePartly eager lazy (globalsTable (allOf eager lazy))).1 ++ lazy.map fun binding => (binding.1, Value.callable binding.2)) =
      Assoc.get name (compileGlobals (allOf eager lazy)) := by
  rw [← compilePartly_forced]
  have hfree {β : Type} (values : List (String × β)) (hv : ∀ binding ∈ values, binding.1 ≠ name) : values.lookup name = none := by
    induction values with
    | nil => rfl
    | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      have hne : (name == key) = false := by
        simpa using Ne.symm (hv (key, value) List.mem_cons_self)
      simp only [List.lookup_cons, hne]
      exact ih fun binding hb => hv binding (List.mem_cons_of_mem _ hb)
  have happ (first second : Globals) (hs : second.lookup name = none) :
      (first ++ second).lookup name = first.lookup name := by
    induction first with
    | nil => simpa using hs
    | cons head tail ih =>
      obtain ⟨key, value⟩ := head
      simp only [List.cons_append, List.lookup_cons, ih]
  simp only [Assoc.get]
  rw [happ, happ]
  · apply hfree
    simp only [compilePartly, List.map_map, List.mem_map]
    rintro _ ⟨binding, hb, rfl⟩
    exact hn binding hb
  · apply hfree
    simp only [List.mem_map]
    rintro _ ⟨binding, hb, rfl⟩
    exact hn binding hb

/-! ### The environment of a target -/

/-- What `liftMC` and `liftWith` run an instruction in. -/
def Environment.state (environment : Environment) : State :=
  { globals := environment.globals, operations := environment.operations }

/-- All of the definitions of a thunked environment. -/
def thunkedAll (eager : Globals) (lazy : List ((String × Callable) × Nat)) : Globals :=
  allOf eager (lazy.map Prod.fst)

private theorem get_append (name : String) (first second : Globals) :
    Assoc.get name (first ++ second) = (Assoc.get name first).or (Assoc.get name second) := by
  simp only [Assoc.get]
  induction first with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    simp only [List.cons_append, List.lookup_cons]
    split <;> simp [ih]

private theorem get_compiled (names : String → Option Bap.Primus.Semantics.Value) (name : String) (values : Globals) :
    Assoc.get name (values.map fun binding => (binding.1, compileValue names binding.2)) =
      (Assoc.get name values).map (compileValue names) := by
  simp only [Assoc.get]
  induction values with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp [ih]

private theorem thunked_names (eager : Globals) (lazy : List ((String × Callable) × Nat)) :
    (fun name => (globalsTable (thunkedAll eager lazy)).get? name) = namesOf (thunkedAll eager lazy) :=
  funext (globalsTable_get (thunkedAll eager lazy))

private theorem thunkedAll_raw (eager : Globals) (lazy : List ((String × Callable) × Nat)) :
    thunkedAll eager lazy = eager ++ lazy.map fun entry => (entry.1.1, Value.callable entry.1.2) := by
  simp [thunkedAll, allOf, List.map_map, Function.comp_def]

/-- The definitions of a thunked environment. -/
theorem thunked_globals (eager : Globals) (lazy : List ((String × Callable) × Nat)) :
    (Environment.thunked eager lazy).globals =
      eager.map (fun binding => (binding.1, compileValue (namesOf (thunkedAll eager lazy)) binding.2)) ++
        lazy.map fun entry => (entry.1.1, Value.callable entry.1.2) := by
  simp only [Environment.thunked, compilePartly, Environment.ofMachine, Environment.ofGlobals, ← thunkedAll_raw, thunked_names]

/-- **The state of a thunked environment is one that compiled code runs in**: each of `eager` compiled, each instruction as it was written. -/
theorem thunked_compat (eager : Globals) (lazy : List ((String × Callable) × Nat)) :
    Compat (thunkedAll eager lazy) (Environment.state (Environment.thunked eager lazy)) where
  definitions name := by
    simp only [Environment.state, thunked_globals]
    rw [get_append, get_compiled, thunkedAll_raw, get_append]
    generalize (lazy.map fun entry => (entry.1.1, Value.callable entry.1.2)) = raw
    cases he : Assoc.get name eager with
    | some value => exact ⟨true, by simp [viewValue]⟩
    | none =>
      refine ⟨false, ?_⟩
      cases Assoc.get name raw <;> simp [viewValue]
  index := ofGlobals_operations _

private theorem table_mem {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] (bindings : List (α × β)) {key : α} {value : β}
    (h : (bindings.reverse.foldl (init := ({} : Std.HashMap α β)) fun result binding => result.insert binding.1 binding.2).get? key = some value) :
    (key, value) ∈ bindings := by
  induction bindings with
  | nil => simp at h
  | cons head rest ih =>
    obtain ⟨first, second⟩ := head
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] at h ih
    split at h
    · next he =>
      simp only [Option.some.injEq] at h
      simp only [beq_iff_eq] at he
      subst he
      subst h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

private theorem zip_map_self {α β : Type} (f : α → β) (values : List α) {pair : β × α} (h : pair ∈ (values.map f).zip values) :
    pair.2 ∈ values ∧ pair.1 = f pair.2 := by
  induction values with
  | nil => simp at h
  | cons head rest ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- **An instruction that a thunked environment lifts by the number of its opcode agrees with the interpreter**: it is the thunk of an instruction of `lazy`
of that number, whatever was forced before, and running what the thunk holds has the same successes as running the instruction as it was written, in
the state `liftMC` runs it in. -/
theorem thunked_opcode_agrees (eager : Globals) (lazy : List ((String × Callable) × Nat)) {opcode : Nat} {thunk : Thunk Callable}
    (h : (Environment.thunked eager lazy).opcodes.get? opcode = some thunk) :
    ∃ entry ∈ lazy, entry.2 = opcode ∧ thunk.get = compileCallable (namesOf (thunkedAll eager lazy)) entry.1.2 ∧
      ∀ (context : Context) (args : List Bap.Primus.Semantics.Value),
        SameResults (fun fuel => apply fuel context (Environment.state (Environment.thunked eager lazy)) (.callable thunk.get) args)
          (fun fuel => apply fuel context (Environment.state (Environment.thunked eager lazy)) (.callable entry.1.2) args) := by
  simp only [Environment.thunked, compilePartly, Environment.ofMachine, ← thunkedAll_raw, thunked_names] at h
  have hm := table_mem _ h
  simp only [List.map_map, List.mem_map] at hm
  obtain ⟨pair, hp, heq⟩ := hm
  obtain ⟨hentry, hthunk⟩ := zip_map_self _ lazy hp
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hopcode, hsame⟩ := heq
  have hget : thunk.get = compileCallable (namesOf (thunkedAll eager lazy)) pair.2.1.2 := by
    subst hsame
    rw [hthunk]
    rfl
  refine ⟨pair.2, hentry, hopcode, hget, fun context args => ?_⟩
  rw [hget]
  exact apply_compileCallable (thunked_compat eager lazy) _ args

/-- **So does one it lifts by name**, in the state of `liftWith`. -/
theorem thunked_instruction_agrees (eager : Globals) (lazy : List ((String × Callable) × Nat)) {name : String} {thunk : Thunk Callable}
    (h : (Environment.thunked eager lazy).instructions.get? name = some thunk) :
    ∃ entry ∈ lazy, entry.1.1 = name ∧ thunk.get = compileCallable (namesOf (thunkedAll eager lazy)) entry.1.2 ∧
      ∀ (context : Context) (args : List Bap.Primus.Semantics.Value),
        SameResults (fun fuel => apply fuel context (Environment.state (Environment.thunked eager lazy)) (.callable thunk.get) args)
          (fun fuel => apply fuel context (Environment.state (Environment.thunked eager lazy)) (.callable entry.1.2) args) := by
  simp only [Environment.thunked, compilePartly, ← thunkedAll_raw, thunked_names] at h
  have hm := table_mem _ h
  simp only [List.map_map, List.mem_map, Prod.mk.injEq, Function.comp_def] at hm
  obtain ⟨entry, hentry, hname, hthunk⟩ := hm
  have hget : thunk.get = compileCallable (namesOf (thunkedAll eager lazy)) entry.1.2 := by
    rw [← hthunk]
    rfl
  refine ⟨entry, hentry, hname, hget, fun context args => ?_⟩
  rw [hget]
  exact apply_compileCallable (thunked_compat eager lazy) _ args


end Bap.Proofs.Primus
