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
open_private Bap.Primus.Semantics Bap.Primus.Semantics evalTopLevel evalFormsIn topLevelState define addDefinition compileValue compileCallable

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

`compilePartly` puts off the compilation of `lazy`. What follows says of it all that `Compat` can say. `Compat` is about the definitions compiled, all of them, so that it
holds of the state of a thunked environment once every instruction was forced (`compilePartly_forced`, `forced_compat`), and of the definitions that are not
instructions in the state that runs (`compilePartly_lookup`). That a state with the instructions as they are there, not compiled, agrees as well needs `Compat`
to be about what a name finds up to compilation, which `compile_agrees` in `Bap.Proofs.Primus` would have to be redone on. -/

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

end Bap.Proofs.Primus
