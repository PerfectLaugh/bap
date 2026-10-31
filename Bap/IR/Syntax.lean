import Bap.Bil.Syntax

namespace Bap.IR

abbrev Tid := Nat

structure Def where
  tid : Tid
  var : Bap.Var
  rhs : Bil.Exp
  deriving Repr

abbrev Arg := Def

structure Phi where
  tid : Tid
  var : Bap.Var
  values : List (Tid × Bil.Exp)
  deriving Repr

inductive Label where
  | direct (tid : Tid)
  | indirect (target : Bil.Exp)
  deriving Repr

inductive JmpKind where
  | goto (target : Label)
  | ret (target : Label)
  | call (target : Label) (returnTo : Option Label)
  | interrupt (number : Nat) (returnTo : Tid)
  deriving Repr

structure Jmp where
  tid : Tid
  condition : Option Bil.Exp
  kind : JmpKind
  deriving Repr

structure Blk where
  tid : Tid
  phis : List Phi := []
  defs : List Def := []
  jmps : List Jmp := []
  deriving Repr

structure Sub where
  tid : Tid
  name : String
  args : List Arg := []
  blks : List Blk := []
  deriving Repr

structure Program where
  subs : List Sub := []
  deriving Repr

end Bap.IR
