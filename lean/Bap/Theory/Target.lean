import Bap.Theory.Value
import Bap.Core.Assoc

namespace Bap.Theory

inductive Endianness where
  | le
  | eb
  | bi
  deriving DecidableEq, Repr

inductive SystemKind where
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
  | hard
  | soft
  deriving DecidableEq, Repr

inductive Filetype where
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
  system : SystemKind := .none
  abi : Abi := .gnu
  fabi : Fabi := .hard
  filetype : Filetype := .elf
  options : String := ""
  specified : List String := []
  deriving DecidableEq, Repr

structure Declaration where
  name : String
  parent : Option Target := none
  nicknames : List String := []
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

/-- The root of the hierarchy, carrying upstream's defaults. Fields whose enumeration has no
`unknown` constructor (`abi`, `fabi`, `filetype`) keep their structure defaults. -/
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
  let specified :=
    (if declaration.bits.isSome then ["bits"] else []) ++
    (if declaration.byte.isSome then ["byte"] else []) ++
    (if declaration.system.isSome then ["system"] else []) ++
    (if declaration.abi.isSome then ["abi"] else []) ++
    (if declaration.fabi.isSome then ["fabi"] else []) ++
    (if declaration.filetype.isSome then ["filetype"] else [])
  {
    name := declaration.name
    nicknames := declaration.nicknames
    parent := some parent.name
    family := parent.name :: parent.family
    bits := declaration.bits.getD parent.bits
    byte := declaration.byte.getD parent.byte
    dataAlignment := declaration.dataAlignment.getD parent.dataAlignment
    codeAlignment := declaration.codeAlignment.getD parent.codeAlignment
    data := declaration.data.orElse fun _ => parent.data
    code := declaration.code.orElse fun _ => parent.code
    vars := declaration.vars.getD parent.vars
    regs := declaration.regs.getD parent.regs
    aliases := declaration.aliases.getD parent.aliases
    endianness := declaration.endianness.getD parent.endianness
    system := declaration.system.getD parent.system
    abi := declaration.abi.getD parent.abi
    fabi := declaration.fabi.getD parent.fabi
    filetype := declaration.filetype.getD parent.filetype
    options := declaration.options.getD parent.options
    specified := specified
  }

def Target.matches (target : Target) (name : String) : Bool :=
  let name := name.toLower
  target.name.toLower = name || target.nicknames.any fun nickname => nickname.toLower = name

def Target.belongs (ancestor target : Target) : Bool :=
  ancestor.name = target.name || target.family.contains ancestor.name

@[simp] theorem Target.belongs_self (target : Target) : target.belongs target = true := by
  simp [Target.belongs]

def Target.parents (target : Target) : List String := target.family

def Target.var (target : Target) (name : String) : Option Var :=
  target.vars.find? fun var => var.name = name

def Target.registers (target : Target) (roles : List Role := []) (exclude : List Role := []) : List Var :=
  (target.regs.filter fun group =>
    (group.1.all fun role => role ∉ exclude) &&
    (roles.isEmpty || group.1.any fun role => role ∈ roles)).flatMap Prod.snd |>.eraseDups

def Target.reg (target : Target) (role : Role) (unique : Bool := false) : Option Var :=
  match target.registers [role] with
  | [var] => some var
  | var :: _ => if unique then none else some var
  | [] => none

/-- Whether `var` has every role in `roles`, each possibly through a different group. As upstream's
`List.for_all`, this holds vacuously for any variable when `roles` is empty. -/
def Target.hasRoles (target : Target) (roles : List Role) (var : Var) : Bool :=
  roles.all fun role => target.regs.any fun group => role ∈ group.1 ∧ var ∈ group.2

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

private def findSub (target : Target) (var : Var) : List Alias → Option Origin
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
              let isAlias := target.aliases.any fun candidate => alias.target ∈ candidate.parts.filterMap aliasPartVar
              some (.sub alias.target (low + width - 1) low isAlias)
            | _, _ => none
          else
            find tail
        | .unknown => find tail
    match find alias.parts with
    | some origin => some origin
    | none => findSub target var rest

def Target.unalias (target : Target) (var : Var) : Option Origin :=
  match findSub target var target.aliases with
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
  parent : Option Target := none
  system : Option SystemKind := none
  abi : Option Abi := none
  fabi : Option Fabi := none
  filetype : Option Filetype := none
  strict : Bool := false
  unique : Bool := false

def filter (selection : Selection) (targets : List Target) : List Target :=
  targets.filter fun target =>
    (selection.parent.all fun parent => parent.belongs target) ∧
    (selection.system.all fun system => target.system = system) ∧
    (selection.abi.all fun abi => target.abi = abi) ∧
    (selection.fabi.all fun fabi => target.fabi = fabi) ∧
    (selection.filetype.all fun filetype => target.filetype = filetype) ∧
    (!selection.strict ||
      ((!selection.system.isSome || "system" ∈ target.specified) &&
       (!selection.abi.isSome || "abi" ∈ target.specified) &&
       (!selection.fabi.isSome || "fabi" ∈ target.specified) &&
       (!selection.filetype.isSome || "filetype" ∈ target.specified)))

def select (selection : Selection) (targets : List Target) : Option Target :=
  match filter selection targets with
  | [target] => some target
  | target :: _ => if selection.unique then none else some target
  | [] => none

def register (target : Target) (registry : List Target) : List Target :=
  target :: registry.filter fun registered => registered.name != target.name

def get (name : String) (registry : List Target) : Option Target :=
  registry.find? fun target => target.matches name

end Bap.Theory
