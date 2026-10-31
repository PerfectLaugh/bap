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
  endianness : Endianness := .bi
  system : SystemKind := .unknown
  abi : Abi := .unknown
  fabi : Fabi := .unknown
  filetype : Filetype := .unknown
  options : String := ""
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
  options : Option String := none

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

def Target.var (target : Target) (name : String) : Option Var :=
  target.vars.find? fun var => var.name = name

def Target.hasRole (target : Target) (var : Var) (role : Role) : Bool :=
  target.regs.any fun group => role ∈ group.1 ∧ var ∈ group.2

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

private def aliasPartVar : AliasPart → Option Var
  | .reg var | .bit var => some var
  | .unknown => none

private def partWidth : AliasPart → Option Nat
  | .reg var => var.sort.bits
  | .bit _ => some 1
  | .unknown => none

private def findSub (var : Var) : List Alias → Option Origin
  | [] => none
  | alias :: rest =>
    let rec find (parts : List AliasPart) : Option Origin :=
      match parts with
      | [] => none
      | part :: tail =>
        let low := (tail.mapM partWidth).map List.sum
        match part with
        | .reg partValue | .bit partValue =>
          if partValue = var then
            match partWidth part, low with
            | some width, some low =>
              some (.sub alias.target (low + width - 1) low false)
            | _, _ => none
          else
            find tail
        | .unknown => find tail
    match find alias.parts with
    | some origin => some origin
    | none => findSub var rest

/-- Follows nested aliases out to the original register, adding up the offsets. The fuel only
matters for cyclic definitions. -/
private def resolveBase (target : Target) : Nat → Var → Nat → Var × Nat
  | 0, base, low => (base, low)
  | fuel + 1, base, low =>
    match findSub base target.aliases with
    | some (.sub outer _ inner _) => resolveBase target fuel outer (low + inner)
    | _ => (base, low)

/-- The origin of a register in terms of the original registers. A `sub` is an alias of its base
when it covers the whole of it. -/
def Target.unalias (target : Target) (var : Var) : Option Origin :=
  match findSub var target.aliases with
  | some (.sub base hi lo _) =>
    let (root, low) := resolveBase target target.aliases.length base lo
    some (.sub root (low + (hi - lo)) low (root.sort.bits == some (hi - lo + 1)))
  | some origin => some origin
  | none =>
    target.aliases.findSome? fun alias =>
      if alias.target = var then
        match alias.parts.mapM aliasPartVar with
        | some vars =>
          if alias.parts.all fun part => match part with | .reg _ => true | _ => false then
            some (.sup vars)
          else if alias.parts.all fun part => match part with | .bit _ => true | _ => false then
            some (.set vars)
          else
            none
        | none => none
      else
        none

structure Selection where
  parent : Target := unknown
  system : SystemKind := .unknown
  abi : Abi := .unknown
  fabi : Fabi := .unknown
  filetype : Filetype := .unknown
  options : String := ""
  strict : Bool := false
  unique : Bool := false

/-- Upstream's matching of a property: strictly it must equal the requirement, otherwise it must be
at least as defined as the requirement in the flat domain whose bottom is `none`. -/
def fieldMatches [DecidableEq α] (strict : Bool) (none : α) (actual wanted : α) : Bool :=
  if strict then actual = wanted else wanted = none || actual = wanted

def filter (selection : Selection) (targets : List Target) : List Target :=
  targets.filter fun target =>
    target.name != unknown.name &&
    selection.parent.belongs target &&
    fieldMatches selection.strict .unknown target.system selection.system &&
    fieldMatches selection.strict .unknown target.abi selection.abi &&
    fieldMatches selection.strict .unknown target.fabi selection.fabi &&
    fieldMatches selection.strict .unknown target.filetype selection.filetype &&
    fieldMatches selection.strict "" target.options selection.options

def select (selection : Selection) (targets : List Target) : Option Target :=
  match filter selection targets with
  | [target] => some target
  | target :: _ => if selection.unique then none else some target
  | [] => none

def register (target : Target) (registry : List Target) : List Target :=
  target :: registry.filter fun registered => registered.name != target.name

/-- The target with exactly this name. Nicknames and ancestors are for `Target.matches`. -/
def get (name : String) (registry : List Target) : Option Target :=
  registry.find? fun target => target.name = name

end Bap.Theory
