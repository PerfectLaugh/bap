import Bap.Bil.Transform

namespace Bap.Analysis.Propagate

abbrev Known := List (Bap.Var × Bil.Exp)

def simplify (known : Known) (exp : Bil.Exp) : Bil.Exp :=
  Bil.foldExp (Bil.substitute known exp)

mutual
  def stmt (known : Known) : Bil.Stmt → Known × Bil.Stmt
    | .move var value =>
      let value := simplify known value
      let known := match value with
        | .int _ => Assoc.put var value known
        | _ => Assoc.remove var known
      (known, .move var value)
    | .jmp target => (known, .jmp (simplify known target))
    | .special message => (known, .special message)
    | .cpuExn number => (known, .cpuExn number)
    | .while condition body =>
      (known, .while (simplify known condition) (program known body).2)
    | .ifElse condition yes no =>
      (known, .ifElse (simplify known condition) (program known yes).2 (program known no).2)

  def program (known : Known) (code : List Bil.Stmt) : Known × List Bil.Stmt :=
    code.foldl (fun current statement =>
      let (known, statement) := stmt current.1 statement
      (known, current.2 ++ [statement])) (known, [])
end

def propagate (code : Bil.Program) : Bil.Program := (program {} code).2

def propagateWithState (known : Known) (code : Bil.Program) : Known × Bil.Program := program known code

end Bap.Analysis.Propagate
