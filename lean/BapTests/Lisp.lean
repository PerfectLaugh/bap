import BapTests.Support

namespace Bap.Tests.Lisp

open Bap
open Bap.Primus.Lisp

private def evaluate (input : String) (fuel : Nat := 100000) : IO String :=
  match evalString input {} fuel with
  | .ok (value, _) => pure (render value)
  | .error error => throw <| IO.userError error

def run : IO Unit := do
  assertEqual "Lisp arithmetic" "0x2a" (← evaluate "(+ 40 2)")
  assertEqual "Lisp multi-form function" "0x2a"
    (← evaluate "(defun add (x y) (+ x y)) (add 40 2)")
  assertEqual "Lisp lexical closure" "0x2a"
    (← evaluate "((lambda (x) ((lambda (y) (+ x y)) 2)) 40)")
  assertEqual "Lisp let binding" "0x2a" (← evaluate "(let ((x 40) (y 2)) (+ x y))")
  assertEqual "Lisp lexical shadowing" "0x15" (← evaluate "(let ((x 10)) ((lambda (x) (+ x 1)) 20))")
  assertEqual "Lisp recursive function" "0x78"
    (← evaluate "(defun fact (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5)")
  assertEqual "Lisp quote" "(0x1 0x2 0x3)" (← evaluate "(quote (1 2 3))")
  assertEqual "Lisp shorthand quote" "Nil" (← evaluate "'Nil")
  assertEqual "Lisp cons and car" "0x1" (← evaluate "(car (cons 1 (quote (2 3))))")
  assertEqual "Lisp cdr" "(0x2 0x3)" (← evaluate "(cdr (quote (1 2 3)))")
  assertEqual "Lisp list length" "0x3" (← evaluate "(length (quote (1 2 3)))")
  assertEqual "Lisp null predicate" "true" (← evaluate "(null? (quote ()))")
  assertEqual "Lisp list predicate" "true" (← evaluate "(list? (quote (1)))")
  assertEqual "Lisp and short circuit" "false" (← evaluate "(and false unknown)")
  assertEqual "Lisp or short circuit" "true" (← evaluate "(or true unknown)")
  assertEqual "Lisp comparison" "true" (← evaluate "(< 1 2)")
  assertEqual "Lisp let bindings see earlier global updates" "0x1"
    (← evaluate "(let ((a (setq g 1)) (b g)) b)")
  assertEqual "Lisp let keeps global updates of every binding" "0x1"
    (← evaluate "(let ((a (setq g 1)) (b 2)) b) g")
  assertEqual "Lisp setq updates a let binding" "0x2" (← evaluate "(let ((x 1)) (setq x 2) x)")
  assertEqual "Lisp setq updates an enclosing let binding" "0x2"
    (← evaluate "(let ((x 1)) (let ((y 5)) (setq x 2)) x)")
  assertEqual "Lisp setq stops at the innermost binding" "0x1"
    (← evaluate "(let ((x 1)) (let ((x 5)) (setq x 2)) x)")
  assertEqual "Lisp setq of a let binding leaves the global" "0x9"
    (← evaluate "(setq x 9) (let ((x 1)) (setq x 2)) x")
  assertEqual "Lisp setq of a free name writes the global" "0x3"
    (← evaluate "(let ((y 1)) (setq z 3)) z")
  assertEqual "Lisp closure assignment stays in its call" "0x1"
    (← evaluate "(let ((x 1)) ((lambda (y) (setq x y)) 7) x)")
  assertEqual "Lisp hexadecimal literal" "0x10" (← evaluate "0x10")
  assertEqual "Lisp binary literal" "0x5" (← evaluate "(+ 0b101 0)")
  assertEqual "Lisp character literal" "<bil 8>" (← evaluate "?a")
  assertEqual "Lisp typed literal" "<bil 16>" (← evaluate "1:16")
  assertEqual "Lisp quoted malformed atom is data" "12x" (← evaluate "'12x")
  for source in ["12x", "0xzz", "1:2:3", "?ab", "?", "(defun f () 9z) (f)"] do
    match evalString source with
    | .error _ => IO.println s!"ok: Lisp rejects {source}"
    | .ok _ => throw <| IO.userError s!"Lisp accepted {source}"
  assertEqual "a symbol that does not start like a number stays one" "0x1" (← evaluate "(setq x1 1) x1")
  match evalString "(unknown-function 1)" with
  | .error _ => IO.println "ok: Lisp unknown symbol rejected"
  | .ok _ => throw <| IO.userError "Lisp unknown symbol accepted"
  match evalString "((lambda (x) x) 1 2)" with
  | .error _ => IO.println "ok: Lisp arity mismatch rejected"
  | .ok _ => throw <| IO.userError "Lisp arity mismatch accepted"
  match evalString "(quote x)" {} 0 with
  | .error _ => IO.println "ok: Lisp fuel exhaustion reported"
  | .ok _ => throw <| IO.userError "Lisp zero-fuel evaluation succeeded"

end Bap.Tests.Lisp
