import Bap.Core.Types
import Bap.Core.Word

namespace Bap.Bil

inductive Cast where
  | low
  | high
  | signed
  | unsigned
  deriving DecidableEq, Repr

inductive UnOp where
  | neg
  | not
  deriving DecidableEq, Repr

inductive BinOp where
  | add
  | sub
  | mul
  | div
  | sdiv
  | rem
  | srem
  | smod
  | lshift
  | rshift
  | ashift
  | and
  | or
  | xor
  | eq
  | neq
  | lt
  | le
  | gt
  | ge
  | slt
  | sle
  | sgt
  | sge
  deriving DecidableEq, Repr

inductive Exp where
  | int {width : Nat} (value : BitVec width)
  | var (var : Bap.Var)
  | load (memory address : Exp) (endian : Endian) (size : Nat)
  | store (memory address value : Exp) (endian : Endian) (size : Nat)
  | bin (op : BinOp) (left right : Exp)
  | un (op : UnOp) (value : Exp)
  | cast (kind : Cast) (width : Nat) (value : Exp)
  | letIn (var : Bap.Var) (value body : Exp)
  | ite (condition yes no : Exp)
  | extract (high low : Nat) (value : Exp)
  | concat (left right : Exp)
  | unknown (message : String) (typ : Typ)
  deriving Repr

inductive Stmt where
  | move (var : Bap.Var) (value : Exp)
  | jmp (target : Exp)
  | special (message : String)
  | while (condition : Exp) (body : List Stmt)
  | ifElse (condition : Exp) (yes no : List Stmt)
  | cpuExn (number : Nat)
  deriving Repr

abbrev Program := List Stmt

end Bap.Bil
