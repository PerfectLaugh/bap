import Bap.Bil.Eval

namespace Bap.Bil

abbrev MemoryObserver := Bool → Nat → Nat → Nat → IO Unit

private def expectMemory : Value → Except String (Σ width, Memory width)
  | .memory value => .ok ⟨_, value⟩
  | _ => .error "expected memory"

private def notify (observer : Option MemoryObserver) (write : Bool) (address size value : Nat) : IO Unit :=
  match observer with
  | some observer => observer write address size value
  | none => pure ()

def evalExpObserved (observer : Option MemoryObserver) (env : Env) (exp : Exp) :
    IO (Except String Value) :=
  match exp with
  | .int value => pure (.ok (.bits value))
  | .var var => pure (lookup env var)
  | .load memory address endian size => do
    match ← evalExpObserved observer env memory with
    | .error error => pure (.error error)
    | .ok memory =>
      match ← evalExpObserved observer env address with
      | .error error => pure (.error error)
      | .ok address =>
        match expectMemory memory, Value.asBits address with
        | .error error, _ => pure (.error error)
        | _, .error error => pure (.error error)
        | .ok ⟨addressWidth, memory⟩, .ok ⟨actualWidth, address⟩ =>
          if h : actualWidth = addressWidth then
            let address : BitVec addressWidth := h ▸ address
            notify observer false address.toNat size 0
            pure (.ok (.bits (Memory.read memory address endian size)))
          else
            pure (.error "address width does not match memory")
  | .store memory address value endian size => do
    match ← evalExpObserved observer env memory with
    | .error error => pure (.error error)
    | .ok memory =>
      match ← evalExpObserved observer env address with
      | .error error => pure (.error error)
      | .ok address =>
        match ← evalExpObserved observer env value with
        | .error error => pure (.error error)
        | .ok value =>
          match expectMemory memory, Value.asBits address, Value.asBits value with
          | .error error, _, _ => pure (.error error)
          | _, .error error, _ => pure (.error error)
          | _, _, .error error => pure (.error error)
          | .ok ⟨addressWidth, memory⟩, .ok ⟨actualWidth, address⟩, .ok stored =>
            if h : actualWidth = addressWidth then
              let address : BitVec addressWidth := h ▸ address
              notify observer true address.toNat size stored.2.toNat
              pure (Memory.write memory address stored.2 endian size |>.map Value.memory)
            else
              pure (.error "address width does not match memory")
  | .bin op left right => do
    match ← evalExpObserved observer env left with
    | .error error => pure (.error error)
    | .ok left =>
      match ← evalExpObserved observer env right with
      | .error error => pure (.error error)
      | .ok right =>
        match Value.asBits left, Value.asBits right with
        | .error error, _ => pure (.error error)
        | _, .error error => pure (.error error)
        | .ok left, .ok right => pure (evalBin op left right)
  | .un op value => do
    match ← evalExpObserved observer env value with
    | .error error => pure (.error error)
    | .ok value => pure (Value.asBits value |>.map fun value =>
      match op with
      | .neg => .bits (-value.2)
      | .not => .bits (~~~value.2))
  | .cast kind width value => do
    match ← evalExpObserved observer env value with
    | .error error => pure (.error error)
    | .ok value => pure (Value.asBits value >>= fun value =>
      match kind with
      | .low => .ok (.bits (Word.low width value.2))
      | .unsigned => .ok (.bits (Word.unsigned width value.2))
      | .signed => .ok (.bits (Word.signed width value.2))
      | .high => Word.high width value.2 |>.map Value.bits)
  | .letIn var value body => do
    match ← evalExpObserved observer env value with
    | .error error => pure (.error error)
    | .ok value => evalExpObserved observer (bind env var value) body
  | .ite condition yes no => do
    match ← evalExpObserved observer env condition with
    | .error error => pure (.error error)
    | .ok condition =>
      match Value.asBits condition with
      | .error error => pure (.error error)
      | .ok ⟨width, condition⟩ =>
        if h : width = 1 then
          let condition : BitVec 1 := h ▸ condition
          evalExpObserved observer env (if condition = 1 then yes else no)
        else
          pure (.error "condition must be one bit")
  | .extract high low value => do
    match ← evalExpObserved observer env value with
    | .error error => pure (.error error)
    | .ok value => pure (Value.asBits value >>= fun value =>
      Word.extract high low value.2 |>.map Value.bits)
  | .concat left right => do
    match ← evalExpObserved observer env left with
    | .error error => pure (.error error)
    | .ok left =>
      match ← evalExpObserved observer env right with
      | .error error => pure (.error error)
      | .ok right => pure (Value.asBits left >>= fun left => Value.asBits right >>= fun right =>
        .ok (.bits (Word.concat left.2 right.2)))
  | .unknown message _ => pure (.error s!"cannot evaluate unknown value: {message}")
  termination_by exp
  decreasing_by
    all_goals simp_wf
    all_goals first | omega | (split <;> omega)

mutual
  def execStmtObserved (observer : Option MemoryObserver) (fuel : Nat) (state : State) (stmt : Stmt) :
      IO (Except String (State × Effect)) := do
    match fuel with
    | 0 => pure (.error "execution fuel exhausted")
    | fuel + 1 =>
      match stmt with
      | .move var value => do
        match ← evalExpObserved observer state.env value with
        | .error error => pure (.error error)
        | .ok value => pure (.ok ({ env := bind state.env var value }, .normal))
      | .jmp target => do
        match ← evalExpObserved observer state.env target with
        | .error error => pure (.error error)
        | .ok target => pure (Value.asBits target |>.map fun target => (state, .jump target.2))
      | .special message => pure (.ok (state, .special message))
      | .cpuExn number => pure (.ok (state, .cpuExn number))
      | .ifElse condition yes no => do
        match ← evalExpObserved observer state.env condition with
        | .error error => pure (.error error)
        | .ok condition =>
          match Value.asBits condition with
          | .error error => pure (.error error)
          | .ok ⟨width, condition⟩ =>
            if h : width = 1 then
              let condition : BitVec 1 := h ▸ condition
              execProgramObserved observer fuel state (if condition = 1 then yes else no)
            else
              pure (.error "condition must be one bit")
      | .while conditionExp body => do
        match ← evalExpObserved observer state.env conditionExp with
        | .error error => pure (.error error)
        | .ok condition =>
          match Value.asBits condition with
          | .error error => pure (.error error)
          | .ok ⟨width, conditionValue⟩ =>
            if h : width = 1 then
              let conditionValue : BitVec 1 := h ▸ conditionValue
              if conditionValue = 1 then
                match ← execProgramObserved observer fuel state body with
                | .error error => pure (.error error)
                | .ok (next, .normal) => execStmtObserved observer fuel next (.while conditionExp body)
                | .ok result => pure (.ok result)
              else
                pure (.ok (state, .normal))
            else
              pure (.error "condition must be one bit")

  def execProgramObserved (observer : Option MemoryObserver) (fuel : Nat) (state : State) (program : Program) :
      IO (Except String (State × Effect)) := do
    match fuel with
    | 0 => pure (.error "execution fuel exhausted")
    | fuel + 1 =>
      match program with
      | [] => pure (.ok (state, .normal))
      | stmt :: rest => do
        match ← execStmtObserved observer fuel state stmt with
        | .error error => pure (.error error)
        | .ok (next, .normal) => execProgramObserved observer fuel next rest
        | .ok result => pure (.ok result)
end

def runObserved (observer : Option MemoryObserver) (program : Program) (initial : State := {})
    (fuel : Nat := 100000) : IO (Except String (State × Effect)) :=
  execProgramObserved observer fuel initial program

end Bap.Bil
