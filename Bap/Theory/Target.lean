import Bap.Theory.Value
import Bap.Core.Assoc

namespace Bap.Theory

inductive Endianness where
  | le
  | eb
  | bi
  deriving DecidableEq, Repr

inductive SystemKind where
  | unknown
  | linux
  | darwin
  | vxworks
  | freebsd
  | openbsd
  | windows
  | msdos
  | uefi
  | none
  deriving DecidableEq, Repr

inductive Abi where
  | unknown
  | gnu
  | eabi
  | gnueabi
  | cdecl
  | stdcall
  | fastcall
  | watcom
  | ms
  deriving DecidableEq, Repr

inductive Fabi where
  | unknown
  | hard
  | soft
  deriving DecidableEq, Repr

inductive Filetype where
  | unknown
  | elf
  | coff
  | macho
  | aout
  deriving DecidableEq, Repr

inductive Role where
  | general
  | special
  | alias
  | pseudo
  | integer
  | floating
  | vector
  | stackPointer
  | framePointer
  | link
  | thread
  | privileged
  | constant
  | zero
  | one
  | status
  | control
  | system
  | zeroFlag
  | signFlag
  | carryFlag
  | overflowFlag
  | parityFlag
  | hardware
  | reserved
  | functionArgument
  | functionReturn
  | callerSaved
  | calleeSaved
  deriving DecidableEq, Repr

inductive AliasPart where
  | reg (var : Var)
  | bit (var : Var)
  | unknown
  deriving DecidableEq, Repr

structure Alias where
  target : Var
  parts : List AliasPart
  deriving DecidableEq, Repr

/-- The options of a target: properties with values, in the partial order of upstream's `Target.Options`, a value of a class
of the Knowledge Base, whose order is pointwise on its slots. The empty options are at the bottom. -/
abbrev Options := List (String × String)

namespace Options

/-- Whether `left` says nothing that `right` doesn't. -/
def le (left right : Options) : Bool := left.all (right.contains ·)

/-- The same properties, whatever their order. -/
def same (left right : Options) : Bool := le left right && le right left

end Options

structure Target where
  name : String
  nicknames : List String := []
  parent : Option String := none
  family : List String := []
  /-- The name and nicknames of each ancestor, nearest first, for `Target.matching`. -/
  lineage : List (String × List String) := []
  bits : Nat := 0
  byte : Nat := 0
  dataAlignment : Nat := 1
  codeAlignment : Nat := 1
  data : Option Var := none
  code : Option Var := none
  vars : List Var := []
  regs : List (List Role × List Var) := []
  aliases : List Alias := []
  /-- The registers that had the `alias` role where `aliases` was declared: what the equations are solved for. -/
  aliased : List Var := []
  endianness : Endianness := .bi
  system : SystemKind := .unknown
  abi : Abi := .unknown
  fabi : Fabi := .unknown
  filetype : Filetype := .unknown
  options : Options := []
  deriving DecidableEq, Repr

structure Declaration where
  name : String
  parent : Option Target := none
  nicknames : Option (List String) := none
  bits : Option Nat := none
  byte : Option Nat := none
  dataAlignment : Option Nat := none
  codeAlignment : Option Nat := none
  data : Option Var := none
  code : Option Var := none
  vars : Option (List Var) := none
  regs : Option (List (List Role × List Var)) := none
  aliases : Option (List Alias) := none
  endianness : Option Endianness := none
  system : Option SystemKind := none
  abi : Option Abi := none
  fabi : Option Fabi := none
  filetype : Option Filetype := none
  options : Option Options := none

/-- The root of the hierarchy, carrying upstream's defaults. -/
def unknown : Target := {
  name := "unknown"
  bits := 32
  byte := 8
  dataAlignment := 8
  codeAlignment := 8
  data := some { name := "mem", sort := .mem 32 8 }
  code := some { name := "mem", sort := .mem 32 8 }
  endianness := .eb
}

/-- A target inherits from its declared parent, or from `unknown` when it names none. -/
def declare (declaration : Declaration) : Target :=
  let parent := declaration.parent.getD unknown
  let data := declaration.data.orElse fun _ => parent.data
  let code := declaration.code.orElse fun _ => parent.code
  let regs := declaration.regs.getD parent.regs
  {
    name := declaration.name
    nicknames := declaration.nicknames.getD parent.nicknames
    parent := some parent.name
    family := parent.name :: parent.family
    lineage := (parent.name, parent.nicknames) :: parent.lineage
    bits := declaration.bits.getD parent.bits
    byte := declaration.byte.getD parent.byte
    dataAlignment := declaration.dataAlignment.getD parent.dataAlignment
    codeAlignment := declaration.codeAlignment.getD parent.codeAlignment
    data := data
    code := code
    vars := (declaration.vars.getD parent.vars ++ data.toList ++ code.toList ++ regs.flatMap Prod.snd).eraseDups
    regs := regs
    aliases := declaration.aliases.getD parent.aliases
    -- A child that does not declare aliases has those of its parent, as solved there, as `Target.extend` upstream, whatever
    -- roles it gives its registers.
    aliased := match declaration.aliases with
      | some _ => (regs.filter fun group => Role.alias ∈ group.1).flatMap Prod.snd
      | none => parent.aliased
    endianness := declaration.endianness.getD parent.endianness
    system := declaration.system.getD parent.system
    abi := declaration.abi.getD parent.abi
    fabi := declaration.fabi.getD parent.fabi
    filetype := declaration.filetype.getD parent.filetype
    options := declaration.options.getD parent.options
  }

def namedBy (name : String) (entry : String × List String) : Bool :=
  let name := name.toLower
  entry.1.toLower = name || entry.2.any fun nickname => nickname.toLower = name

/-- The name of the target or its closest ancestor known by `name`, ignoring case. -/
def Target.matching (target : Target) (name : String) : Option String :=
  (((target.name, target.nicknames) :: target.lineage).find? (namedBy name)).map Prod.fst

def Target.matches (target : Target) (name : String) : Bool :=
  (target.matching name).isSome

def Target.belongs (ancestor target : Target) : Bool :=
  ancestor.name = target.name || target.family.contains ancestor.name

@[simp] theorem Target.belongs_self (target : Target) : target.belongs target = true := by
  simp [Target.belongs]

def Target.parents (target : Target) : List String := target.family

/-- The variable of a name, which registers have whatever their case. -/
def Target.var (target : Target) (name : String) : Option Var :=
  let name := name.toLower
  target.vars.find? fun var => var.name.toLower = name

def Target.hasRole (target : Target) (var : Var) (role : Role) : Bool :=
  target.regs.any fun group => role ∈ group.1 ∧ group.2.any (var.sameReg ·)

/-- The registers that have all of `roles` and none of `exclude`. Roles are properties of a
register, not of a group, so they may come from different groups. -/
def Target.registers (target : Target) (roles : List Role := []) (exclude : List Role := []) : List Var :=
  ((target.regs.filter fun group => !group.1.isEmpty).flatMap Prod.snd).eraseDups.filter fun var =>
    roles.all (target.hasRole var) && !exclude.any (target.hasRole var)

def Target.reg (target : Target) (role : Role) (unique : Bool := false) (exclude : List Role := []) :
    Option Var :=
  match target.registers [role] exclude with
  | [var] => some var
  | var :: _ => if unique then none else some var
  | [] => none

/-- Whether `var` has every role in `roles`, each possibly through a different group. As upstream's
`List.for_all`, this holds vacuously for any variable when `roles` is empty. -/
def Target.hasRoles (target : Target) (roles : List Role) (var : Var) : Bool :=
  roles.all (target.hasRole var)

inductive Origin where
  | sub (reg : Var) (hi lo : Nat) (isAlias : Bool)
  | sup (regs : List Var)
  | set (bits : List Var)
  deriving DecidableEq, Repr

/-- The number of bits of a register. -/
def regWidth (var : Var) : Option Nat :=
  match var.sort with
  | .bitv width => some width
  | .bool => some 1
  | _ => none

/-- A part of a definition as an equation: the bits of `var` are the `width` bits of the defined
register that start at `offset`. -/
structure AliasSpan where
  var : Var
  offset : Nat
  width : Nat
  deriving DecidableEq, Repr

/-- Lays parts out from the end of the list, which is the least significant one. Returns their size. -/
private def layoutParts (hole : Nat) : List AliasPart → Option (Nat × List AliasSpan)
  | [] => some (0, [])
  | part :: rest => do
    let (low, spans) ← layoutParts hole rest
    match part with
    | .unknown => some (low + hole, spans)
    | .reg var | .bit var =>
      let width ← regWidth var
      some (low + width, ⟨var, low, width⟩ :: spans)

/-- The equations of a definition, or nothing if the parts do not add up to the defined register. The
unknown parts share what the others leave. For the equal parts that upstream's `Alias.def` requires
this is its layout; that function raises where this returns nothing. -/
def Alias.spans (alias : Alias) : Option (List AliasSpan) := do
  let total ← regWidth alias.target
  let (known, _) ← layoutParts 0 alias.parts
  let holes := alias.parts.countP fun part => part == .unknown
  let (size, spans) ← layoutParts (if holes = 0 then 0 else (total - known) / holes) alias.parts
  if size = total then some spans else none

/-- The bits that are equal to a bit of a register by a single equation, in either direction. -/
def Target.linked (target : Target) (var : Var) (index : Nat) : List (Var × Nat) :=
  target.aliases.flatMap fun alias =>
    (alias.spans.getD []).filterMap fun span =>
      if alias.target = var ∧ span.offset ≤ index ∧ index < span.offset + span.width then
        some (span.var, index - span.offset)
      else if span.var = var ∧ index < span.width then
        some (alias.target, span.offset + index)
      else
        none

/-- Registers without the `alias` role where the aliases were declared are the basis, as upstream's `Alias.solve`. -/
def Target.isAlias (target : Target) (var : Var) : Bool := target.aliased.any (var.sameReg ·)

/-- The equations of a table, each one saying that two bits are equal. -/
def Target.equations (target : Target) : List ((Var × Nat) × (Var × Nat)) :=
  target.aliases.flatMap fun alias =>
    (alias.spans.getD []).flatMap fun span =>
      (List.range span.width).map fun index => ((span.var, index), (alias.target, span.offset + index))

/-- Adds an equation to a partition, given by the representative of each bit: the classes of its bits become one. -/
def mergeBits (rep : Var × Nat → Var × Nat) (equation : (Var × Nat) × (Var × Nat)) : Var × Nat → Var × Nat :=
  let left := rep equation.1
  let right := rep equation.2
  fun bit =>
    let current := rep bit
    if current = left then right else current

/-- The representative of each bit, when bits that equations relate are the same. -/
def Target.representative (target : Target) : Var × Nat → Var × Nat := target.equations.foldl mergeBits id

/-- Whether a bit is a bit of a register of the basis. -/
def Target.isBasisBit (target : Target) (bit : Var × Nat) : Bool :=
  !target.isAlias bit.1 && (regWidth bit.1).any (bit.2 < ·)

/-- The bits of the basis the equations mention. -/
def Target.basisBits (target : Target) : List (Var × Nat) :=
  ((target.equations.flatMap fun equation => [equation.1, equation.2]).filter target.isBasisBit).eraseDups

/-- The pairs of different bits of a list that have the same representative. -/
def conflictsOf (rep : Var × Nat → Var × Nat) : List (Var × Nat) → List ((Var × Nat) × (Var × Nat))
  | [] => []
  | bit :: rest =>
    (rest.filter fun other => other != bit && rep other == rep bit).map (bit, ·) ++ conflictsOf rep rest

/-- The same of bits with their representatives, each one found once. -/
def conflictsOfTagged : List ((Var × Nat) × (Var × Nat)) → List ((Var × Nat) × (Var × Nat))
  | [] => []
  | (bit, rep) :: rest =>
    (rest.filter fun other => other.2 == rep && other.1 != bit).map (fun other => (bit, other.1)) ++ conflictsOfTagged rest

def conflictsOfFast (rep : Var × Nat → Var × Nat) (bits : List (Var × Nat)) : List ((Var × Nat) × (Var × Nat)) :=
  conflictsOfTagged (bits.map fun bit => (bit, rep bit))

/-- A representative takes a walk through all the equations, so the pairs of bits don't ask for it again. -/
@[csimp] theorem conflictsOf_eq_fast : @conflictsOf = @conflictsOfFast := by
  funext rep bits
  unfold conflictsOfFast
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    simp only [conflictsOf, List.map_cons, conflictsOfTagged, ih, List.filter_map, List.map_map]
    congr 2
    refine List.filter_congr fun other _ => ?_
    simp only [Function.comp_apply, Bool.and_comm]

/-- The pairs of different bits of the basis that the equations of a table make equal. A table with such a pair is overdetermined:
its aliases can't be solved for the basis, which is not free. -/
def Target.conflicts (target : Target) : List ((Var × Nat) × (Var × Nat)) :=
  conflictsOf target.representative target.basisBits

/-- A representative through a table of the bits that aren't their own. -/
def bitLookup : List ((Var × Nat) × (Var × Nat)) → Var × Nat → Var × Nat
  | [], bit => bit
  | entry :: rest, bit => if bit = entry.1 then entry.2 else bitLookup rest bit

/-- `mergeBits` on a table. The closures of `mergeBits` walk every equation on each lookup, three times over, as the
compiler moves its `let`s under the lambda. -/
def mergeTable (table : List ((Var × Nat) × (Var × Nat))) (equation : (Var × Nat) × (Var × Nat)) :
    List ((Var × Nat) × (Var × Nat)) :=
  let left := bitLookup table equation.1
  let right := bitLookup table equation.2
  let mapped := table.map fun entry => (entry.1, if entry.2 = left then right else entry.2)
  if table.any (fun entry => entry.1 = left) then mapped else (left, right) :: mapped

private theorem bitLookup_absent {table : List ((Var × Nat) × (Var × Nat))} {bit : Var × Nat}
    (h : (table.any fun entry => entry.1 = bit) = false) : bitLookup table bit = bit := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    have hne : bit ≠ entry.1 := Ne.symm h.1
    simp only [bitLookup, hne, ↓reduceIte]
    exact ih h.2

private theorem bitLookup_map (table : List ((Var × Nat) × (Var × Nat))) (f : Var × Nat → Var × Nat) (bit : Var × Nat) :
    bitLookup (table.map fun entry => (entry.1, f entry.2)) bit =
      if (table.any fun entry => entry.1 = bit) = true then f (bitLookup table bit) else bit := by
  induction table with
  | nil => simp [bitLookup]
  | cons entry rest ih =>
    simp only [List.map_cons, bitLookup, List.any_cons, ih]
    by_cases h : bit = entry.1
    · simp [h]
    · have h' : decide (entry.1 = bit) = false := decide_eq_false (Ne.symm h)
      simp only [h, ↓reduceIte, h', Bool.false_or]

theorem bitLookup_mergeTable (table : List ((Var × Nat) × (Var × Nat))) (equation : (Var × Nat) × (Var × Nat)) :
    bitLookup (mergeTable table equation) = mergeBits (bitLookup table) equation := by
  funext bit
  simp only [mergeTable, mergeBits]
  generalize bitLookup table equation.1 = left
  generalize bitLookup table equation.2 = right
  have hmap := bitLookup_map table (fun value => if value = left then right else value) bit
  by_cases hb : (table.any fun entry => entry.1 = bit) = true
  · simp only [hb, ↓reduceIte] at hmap
    by_cases hk : (table.any fun entry => entry.1 = left) = true
    · simp only [hk, ↓reduceIte]
      exact hmap
    · have hk' := Bool.eq_false_iff.2 hk
      have hne : bit ≠ left := fun e => hk (e ▸ hb)
      simp only [hk', Bool.false_eq_true, ↓reduceIte, bitLookup, hne]
      exact hmap
  · have hb' := Bool.eq_false_iff.2 hb
    simp only [hb', Bool.false_eq_true, ↓reduceIte] at hmap
    rw [bitLookup_absent hb']
    by_cases hk : (table.any fun entry => entry.1 = left) = true
    · have hne : bit ≠ left := fun e => hb (e ▸ hk)
      simp only [hk, ↓reduceIte, hne]
      exact hmap
    · have hk' := Bool.eq_false_iff.2 hk
      by_cases he : bit = left
      · simp [hk', he, bitLookup]
      · simp only [hk', Bool.false_eq_true, ↓reduceIte, bitLookup, he]
        exact hmap

private theorem foldl_mergeTable (equations : List ((Var × Nat) × (Var × Nat)))
    (table : List ((Var × Nat) × (Var × Nat))) :
    bitLookup (equations.foldl mergeTable table) = equations.foldl mergeBits (bitLookup table) := by
  induction equations generalizing table with
  | nil => rfl
  | cons equation rest ih =>
    simp only [List.foldl_cons]
    rw [ih, bitLookup_mergeTable]

/-- `Target.conflicts` that finds each representative once, through one table. -/
def Target.conflictsFast (target : Target) : List ((Var × Nat) × (Var × Nat)) :=
  let table := target.equations.foldl mergeTable []
  conflictsOfTagged (target.basisBits.map fun bit => (bit, bitLookup table bit))

@[csimp] theorem Target.conflicts_eq_fast : @Target.conflicts = @Target.conflictsFast := by
  funext target
  have hrep : target.representative = bitLookup (target.equations.foldl mergeTable []) := by
    rw [foldl_mergeTable]
    have : bitLookup [] = id := by
      funext bit
      rfl
    rw [this]
    rfl
  simp only [Target.conflicts, Target.conflictsFast, conflictsOf_eq_fast, conflictsOfFast, hrep]

/-- Whether the equations of a table have an independent basis, as upstream's `Alias.solve` assumes without a check. -/
def Target.resolves (target : Target) : Bool := target.conflicts.isEmpty

/-- A table with an independent basis, or what its equations make equal that should not be. -/
def Target.validate (target : Target) : Except String Target :=
  match target.conflicts with
  | [] => .ok target
  | ((left, at₁), (right, at₂)) :: _ =>
    .error s!"the aliases of {target.name} are overdetermined: they make bit {at₁} of {left.name} and bit {at₂} of {right.name} equal"

/-- Searches the equations for the bit of a basis register that a bit of a register is equal to. -/
def Target.locate (target : Target) : Nat → List (Var × Nat) → Var → Nat → Option (Var × Nat)
  | 0, _, _, _ => none
  | fuel + 1, seen, var, index =>
    if target.isAlias var then
      (target.linked var index).findSome? fun bit =>
        if bit ∈ (var, index) :: seen then none else target.locate fuel ((var, index) :: seen) bit.1 bit.2
    else if (regWidth var).any (index < ·) then
      some (var, index)
    else
      none

/-- No path through the equations needs more steps than there are registers in them. -/
def Target.aliasFuel (target : Target) : Nat :=
  (target.aliases.map fun alias => alias.parts.length + 1).sum + 1

def wholeBits (var : Var) : List (Var × Nat) :=
  (List.range ((regWidth var).getD 0)).map (var, ·)

/-- The bits of the basis that an origin denotes, least significant first. -/
def Origin.locations : Origin → List (Var × Nat)
  | .sub reg hi lo _ => (List.range (hi - lo + 1)).map fun index => (reg, lo + index)
  | .sup regs | .set regs => regs.reverse.flatMap wholeBits

/-- The registers of a sequence of bits, in their order, with repetitions collapsed. -/
private def bitRegisters : List (Var × Nat) → List Var
  | [] => []
  | bit :: rest =>
    match bitRegisters rest with
    | reg :: regs => if reg = bit.1 then reg :: regs else bit.1 :: reg :: regs
    | [] => [bit.1]

/-- The origin that denotes exactly these bits, if any can: a contiguous range of a register, or a
concatenation of whole registers. Upstream's `Sub` of a wider alias reports a range outside of its
base; such a register has no origin here. -/
private def originOf (bits : List (Var × Nat)) : Option Origin :=
  match bits with
  | [] => none
  | (reg, lo) :: _ =>
    let sub := Origin.sub reg (lo + bits.length - 1) lo (regWidth reg == some bits.length)
    let regs := (bitRegisters bits).reverse
    if sub.locations = bits then
      some sub
    else if regs.reverse.flatMap wholeBits = bits then
      if regs.all (·.sort == .bool) then some (.set regs)
      else if regs.all (·.sort.bits.isSome) then some (.sup regs)
      else none
    else
      none

/-- The origin of an alias in terms of the basis registers, as upstream's `Target.unalias`: `reg` of a
`sub` is a basis register, whatever the nesting, `hi` and `lo` are the inclusive bounds of the alias in
it, and `isAlias` says that it is all of it; the registers of a `sup` or `set` are basis registers,
most significant first. A basis register has no origin.

Upstream solves the equations in `Target.declare`, and raises when they have no solution. That would
make `declare` partial, so here they are solved on demand and an alias they do not define has no
origin. -/
def Target.unalias (target : Target) (var : Var) : Option Origin :=
  if target.isAlias var then
    match regWidth var with
    | some width => ((List.range width).mapM (target.locate target.aliasFuel [] var)).bind originOf
    | none => none
  else
    none

structure Selection where
  parent : Target := unknown
  system : SystemKind := .unknown
  abi : Abi := .unknown
  fabi : Fabi := .unknown
  filetype : Filetype := .unknown
  options : Options := []
  strict : Bool := false
  unique : Bool := false

/-- Upstream's matching of a property: strictly it must equal the requirement, otherwise it must be
at least as defined as the requirement in the flat domain whose bottom is `none`. -/
def fieldMatches [DecidableEq α] (strict : Bool) (none : α) (actual wanted : α) : Bool :=
  if strict then actual = wanted else wanted = none || actual = wanted

/-- The same for options, which are partially ordered: strictly the same properties, otherwise at least those wanted. -/
def optionsMatch (strict : Bool) (actual wanted : Options) : Bool :=
  if strict then Options.same actual wanted else Options.le wanted actual

def filter (selection : Selection) (targets : List Target) : List Target :=
  targets.filter fun target =>
    target.name != unknown.name &&
    selection.parent.belongs target &&
    fieldMatches selection.strict .unknown target.system selection.system &&
    fieldMatches selection.strict .unknown target.abi selection.abi &&
    fieldMatches selection.strict .unknown target.fabi selection.fabi &&
    fieldMatches selection.strict .unknown target.filetype selection.filetype &&
    optionsMatch selection.strict target.options selection.options

/-- The candidate with the fewest ancestors, the first of those: an ancestor comes before what descends from it, however they
were registered. -/
def closest (first : Target) (rest : List Target) : Target :=
  rest.foldl (fun best target => if target.family.length < best.family.length then target else best) first

def select (selection : Selection) (targets : List Target) : Option Target :=
  match filter selection targets with
  | [target] => some target
  | target :: rest => if selection.unique then none else some (closest target rest)
  | [] => none

/-- Adds a target to a registry. A name is taken once, as upstream's `Target.declare` fails on one that exists: replacing a
target would change what targets that were declared under it, and the parents they name, mean. -/
def register (target : Target) (registry : List Target) : Except String (List Target) :=
  if registry.any fun registered => registered.name == target.name then
    .error s!"a target with name {target.name} already exists"
  else
    .ok (target :: registry)

/-- The target with exactly this name. Nicknames and ancestors are for `Target.matches`. -/
def get (name : String) (registry : List Target) : Option Target :=
  registry.find? fun target => target.name = name

end Bap.Theory
