import Bap.Bil.Eval

namespace Bap.Bil

inductive Step : State → Program → State → Program → Effect → Prop where
  | move (state : State) (var : Bap.Var) (exp : Exp) (value : Value) (rest : Program) :
      execExp state exp = .ok value →
      Step state (.move var exp :: rest) { env := bind state.env var value } rest .normal
  | jump (state : State) (target : Exp) (address : BitVec width) (rest : Program) :
      execExp state target = .ok (Value.bits address) →
      Step state (.jmp target :: rest) state [] (.jump address)
  | ifTrue (state : State) (condition : Exp) (yes no rest : Program) :
      execExp state condition = .ok (Value.bits (BitVec.ofNat 1 1)) →
      Step state (.ifElse condition yes no :: rest) state (yes ++ rest) .normal
  | ifFalse (state : State) (condition : Exp) (yes no rest : Program) :
      execExp state condition = .ok (Value.bits (BitVec.zero 1)) →
      Step state (.ifElse condition yes no :: rest) state (no ++ rest) .normal
  | whileTrue (state : State) (condition : Exp) (body rest : Program) :
      execExp state condition = .ok (Value.bits (BitVec.ofNat 1 1)) →
      Step state (.while condition body :: rest) state
        (body ++ .while condition body :: rest) .normal
  | whileFalse (state : State) (condition : Exp) (body rest : Program) :
      execExp state condition = .ok (Value.bits (BitVec.zero 1)) →
      Step state (.while condition body :: rest) state rest .normal
  | special (state : State) (message : String) (rest : Program) :
      Step state (.special message :: rest) state [] (.special message)
  | cpuExn (state : State) (number : Nat) (rest : Program) :
      Step state (.cpuExn number :: rest) state [] (.cpuExn number)

theorem execProgram_empty (fuel : Nat) (state : State) :
    execProgram (fuel + 1) state [] = .ok (state, .normal) := by
  rfl

theorem execStmt_move_sound (fuel : Nat) (state : State) (var : Bap.Var) (exp : Exp) (value : Value)
    (h : execExp state exp = .ok value) :
    execStmt (fuel + 1) state (.move var exp) = .ok ({ env := bind state.env var value }, .normal) := by
  simp only [execStmt]
  rw [h]
  rfl

theorem step_if_true (state : State) (yes no rest : Program) :
    Step state (.ifElse (.int (BitVec.ofNat 1 1)) yes no :: rest) state (yes ++ rest) .normal := by
  apply Step.ifTrue
  rfl

theorem step_while_false (state : State) (body rest : Program) :
    Step state (.while (.int (BitVec.zero 1)) body :: rest) state rest .normal := by
  apply Step.whileFalse
  rfl

end Bap.Bil
