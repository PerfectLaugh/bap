import BapTests.Support

namespace Bap.Tests.Ssa

open Bap
open Bap.Bil
open Bap.IR

private def x : Var := ⟨"x", .imm 32, 0, false⟩
private def y : Var := ⟨"y", .imm 32, 0, false⟩
private def int (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
private def defn (tid : Tid) (var : Var) (rhs : Exp) : Def := ⟨tid, var, rhs⟩
private def goto (tid destination : Tid) : Jmp := ⟨tid, none, .goto (.direct destination)⟩
private def expString (exp : Exp) : String := toString (Wire.printExp exp)

private def sample : Sub :=
  {
    tid := 1
    name := "diamond"
    blks := [
      ⟨1, [], [defn 1 x (int 0)], [goto 1 2, goto 2 3]⟩,
      ⟨2, [], [defn 2 x (int 1)], [goto 3 4]⟩,
      ⟨3, [], [defn 3 x (int 2)], [goto 4 4]⟩,
      ⟨4, [], [defn 4 y (.var x)], []⟩,
      ⟨99, [], [defn 99 x (int 7)], []⟩
    ]
  }

private def sampleForIdempotence : Sub := sample

/-- Blocks 2 and 3 are siblings; block 2 assigns `x` twice and block 3 reads `x`. -/
private def siblings : Sub :=
  ⟨1, "siblings", [], [
    ⟨1, [], [], [goto 1 2, goto 2 3]⟩,
    ⟨2, [], [defn 3 x (int 1), defn 4 x (int 2)], []⟩,
    ⟨3, [], [defn 5 y (.var x)], []⟩]⟩

/-- `A: y := x; ret; R: x := 1; goto A`: execution enters at `A`, which also has the root `R` above it. -/
private def entryWithRoot : Sub :=
  ⟨1, "entry-with-root", [], [
    ⟨1, [], [defn 1 y (.var x)], []⟩,
    ⟨2, [], [defn 2 x (int 1)], [goto 3 1]⟩]⟩

/-- `L: y := x; x := 1; goto L`: the entry block is a loop header. -/
private def entryLoop : Sub :=
  ⟨1, "entry-loop", [], [⟨1, [], [defn 1 y (.var x), defn 2 x (int 1)], [goto 3 1]⟩]⟩

/-- `x.1` and `x.2` are different variables: `x.2 := 7; y := x.1`. -/
private def versionedInput : Sub :=
  ⟨1, "versioned", [], [⟨1, [], [defn 1 (x.version 2) (int 7), defn 2 y (.var (x.version 1))], []⟩]⟩

private def plusOne (var : Var) : Exp := .bin .add (.var var) (int 1)

/-- A phi with a non-variable input: `A: x := 1; goto J; J: y := phi(A: x + 1)`. -/
private def computedInput : Sub :=
  ⟨1, "computed-input", [], [
    ⟨1, [], [defn 1 x (int 1)], [goto 2 2]⟩,
    ⟨2, [⟨3, y, [(1, plusOne x)]⟩], [], []⟩]⟩

/-- A join whose input already has a phi for the variable that the arms assign. -/
private def existingPhi : Sub :=
  ⟨1, "existing-phi", [], [
    ⟨1, [], [], [⟨1, some (.var y), .goto (.direct 2)⟩, goto 2 3]⟩,
    ⟨2, [], [defn 3 x (int 1)], [goto 4 4]⟩,
    ⟨3, [], [defn 5 x (int 2)], [goto 6 4]⟩,
    ⟨4, [⟨7, x, [(2, int 10), (3, int 20)]⟩], [defn 8 y (.var x)], []⟩]⟩

/-- Executes a subroutine by the reference semantics of `Bap.Proofs.IR` until no jump has a target. -/
private def execute (sub : Sub) (env : Env) : Nat → Tid → Tid → List Tid → Except String (List Tid × Env)
  | 0, _, _, path => .ok (path.reverse, env)
  | fuel + 1, pred, tid, path =>
    match sub.block tid with
    | none => .error s!"no block {tid}"
    | some blk => do
      let env₁ ← Proofs.IR.execPhis pred env blk.phis env
      let (env₂, _) ← Proofs.IR.execDefs env₁ blk.defs
      match ← Proofs.IR.selectJmp env₂ blk.jmps with
      | none => .ok ((tid :: path).reverse, env₂)
      | some jmp =>
        match jmp.successors with
        | [next] => execute sub env₂ fuel tid next (tid :: path)
        | _ => .ok ((tid :: path).reverse, env₂)

private def runFrom (sub : Sub) (env : Env) : Except String (List Tid × Env) :=
  match sub.blks.head? with
  | some entry => execute sub env 32 pseudoStart entry.tid []
  | none => .ok ([], env)

private def bit (value : Nat) : Value := .bits (BitVec.ofNat 1 value)
private def word (value : Nat) : Value := .bits (BitVec.ofNat 32 value)
private def c : Var := ⟨"c", .imm 1, 0, false⟩

/-- `if c goto A else B; A: x := 1; B: y := x`, with `x` possibly unbound on entry. -/
private def oneArm : Sub :=
  ⟨1, "one-arm", [], [
    ⟨1, [], [], [⟨1, some (.var c), .goto (.direct 2)⟩, goto 2 3]⟩,
    ⟨2, [], [defn 3 x (int 1)], [goto 4 3]⟩,
    ⟨3, [], [defn 5 y (.var c)], []⟩]⟩

/-- The two phis exchange `x` and `y` on the back edge, reading the values on entry to the block: the
second time round `x` is 2 and the loop ends. -/
private def swapLoop : Sub :=
  ⟨1, "swap-loop", [], [
    ⟨1, [], [defn 1 x (int 1), defn 2 y (int 2)], [goto 3 2]⟩,
    ⟨2, [⟨4, x, [(1, .var x), (2, .var y)]⟩, ⟨5, y, [(1, .var y), (2, .var x)]⟩], [],
      [⟨6, some (.bin .eq (.var x) (int 2)), .goto (.direct 3)⟩, goto 7 2]⟩,
    ⟨3, [], [], []⟩]⟩

private def showRead (env : Env) (var : Var) : String :=
  match lookup env var with
  | .ok value => reprStr value
  | .error message => message

/-- The output runs the same path as the input and gives the last write to `var` its value. -/
private def assertRuns (name : String) (sub : Sub) (env : Env) (var : Var) : IO Unit := do
  match runFrom sub env, runFrom (toSsa sub) env with
  | .ok (path, final), .ok (path', final') =>
    assertEqual s!"{name}: same path" path path'
    let versions := ((toSsa sub).blks.reverse.filter (path.contains ·.tid)).flatMap Blk.definedVars
    let read := (versions.filter (·.base == var)).head?.getD var
    assertEqual s!"{name}: same value" (showRead final var) (showRead final' read)
  | .error message, _ => throw <| IO.userError s!"{name}: input failed: {message}"
  | _, .error message => throw <| IO.userError s!"{name}: output failed: {message}"

private def semantics : IO Unit := do
  assertRuns "taken branch" oneArm [(c, bit 1)] x
  assertRuns "untaken branch, unbound on the path" oneArm [(c, bit 0)] y
  assertRuns "untaken branch keeps the entry value" oneArm [(c, bit 0), (x, word 9)] x
  assertRuns "phis exchanging values around a loop" swapLoop [] x
  assertEqual "the exchange takes one trip round" (some [1, 2, 2, 3]) ((runFrom swapLoop []).toOption.map (·.1))
  assertEqual "condition decides the path" (some [1, 3]) ((runFrom oneArm [(c, bit 0)]).toOption.map (·.1))
  assertEqual "condition decides the path when taken" (some [1, 2, 3]) ((runFrom oneArm [(c, bit 1)]).toOption.map (·.1))
  match Proofs.IR.execPhis 2 [(x, word 1), (y, word 2)]
      [⟨4, x, [(2, .var y)]⟩, ⟨5, y, [(2, .var x)]⟩] [(x, word 1), (y, word 2)] with
  | .ok env =>
    assertEqual "phis read simultaneously" (reprStr (word 2)) (showRead env x)
    assertEqual "whatever their order" (reprStr (word 1)) (showRead env y)
  | .error message => throw <| IO.userError message
  match Proofs.IR.execPhis 9 [] [⟨4, x, [(2, .var y)]⟩] [] with
  | .ok _ => throw <| IO.userError "a phi without an input for the predecessor must fail"
  | .error _ => pure ()
  match Proofs.IR.execPhis 2 [(x, word 1)] [⟨4, x, [(2, .var y)]⟩] [(x, word 1)] with
  | .ok env => assertTrue "copying an undefined value leaves the variable undefined" (showRead env x == "unbound variable x")
  | .error message => throw <| IO.userError message

private def regressions : IO Unit := do
  semantics
  match (toSsa entryWithRoot).block 1 with
  | some entry =>
    match entry.phis, entry.defs with
    | [phi], [read] =>
      assertEqual "the entry keeps the value it was entered with"
        (some (expString (.var x))) ((Assoc.get pseudoStart phi.values).map expString)
      assertEqual "the root's write reaches the entry through the phi"
        (some (expString (.var (x.version 2)))) ((Assoc.get 2 phi.values).map expString)
      assertEqual "the read sees the phi" (expString (.var phi.var)) (expString read.rhs)
    | _, _ => throw <| IO.userError "missing entry phi or read"
  | none => throw <| IO.userError "missing entry block"
  match (toSsa entryLoop).block 1 with
  | some header =>
    match header.phis.filter (·.var.base == x), header.defs with
    | [phi], [read, write] =>
      assertEqual "a loop header at the entry has an input for the entry edge"
        (some (expString (.var x))) ((Assoc.get pseudoStart phi.values).map expString)
      assertEqual "and for the back edge" (some (expString (.var write.var))) ((Assoc.get 1 phi.values).map expString)
      assertEqual "the first read is the phi" (expString (.var phi.var)) (expString read.rhs)
    | _, _ => throw <| IO.userError "missing loop header statements"
  | none => throw <| IO.userError "missing loop header"
  match (toSsa versionedInput).block 1 with
  | some block =>
    match block.defs with
    | [write, read] =>
      assertEqual "reading another version is not the write" (expString (.var (x.version 1))) (expString read.rhs)
      assertTrue "issued versions avoid those of the input" (write.var.index > 2)
    | _ => throw <| IO.userError "missing versioned definitions"
  | none => throw <| IO.userError "missing versioned block"
  let once := toSsa sampleForIdempotence
  let twice := toSsa once
  let names := twice.blks.flatMap Blk.definedVars
  assertEqual "SSA of SSA keeps single assignment" names.length names.eraseDups.length
  match (toSsa computedInput).block 2 with
  | some join =>
    match join.phis with
    | [phi] =>
      assertEqual "a computed phi input is renamed like a plain one"
        (some (expString (plusOne (x.version 1)))) ((Assoc.get 1 phi.values).map expString)
    | _ => throw <| IO.userError "missing computed phi"
  | none => throw <| IO.userError "missing computed join"
  match (toSsa existingPhi).block 4 with
  | some join =>
    assertEqual "an existing phi is not doubled" 1 (join.phis.filter (·.var.base == x)).length
    match join.phis, join.defs with
    | [phi], [read] =>
      assertEqual "the existing phi keeps its inputs" (some (expString (int 10))) ((Assoc.get 2 phi.values).map expString)
      assertEqual "reads see the existing phi" (expString (.var phi.var)) (expString read.rhs)
    | _, _ => throw <| IO.userError "missing existing phi"
  | none => throw <| IO.userError "missing join"
  -- The join of a variable written on one arm only has a phi; on a straight line nothing does.
  let straight : Sub := ⟨1, "straight", [], [⟨1, [], [defn 1 x (int 1)], [goto 2 2]⟩, ⟨2, [], [defn 3 y (.var x)], []⟩]⟩
  assertEqual "no phi without a join" [0, 0] ((toSsa straight).blks.map (·.phis.length))

local macro "insertAllPhis" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.insertAllPhis)
local macro "renameBlock" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.renameBlock)
local macro "initialState" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.initialState)

/-- `toSsa` as it reads, where each phi goes over all the blocks: the code it runs places them from tables. -/
private def ssaBySpec (sub : Sub) : Sub :=
  let cfg := Cfg.connected sub
  let idom := cfg.immediateDominators
  let frontier := cfg.dominanceFrontier
  let state := initialState cfg.blocks
  let cfg := insertAllPhis cfg frontier (cfg.blocks.flatMap Blk.definedVars).eraseDups
  let (cfg, _) := renameBlock idom (cfg.blocks.length + 1) cfg.start cfg state
  { sub with blks := sub.blks.filterMap fun blk => cfg.block blk.tid }

private def sameSsa (name : String) (sub : Sub) : IO Unit :=
  assertEqual s!"SSA of {name}" (toString (Wire.printSub (ssaBySpec sub))) (toString (Wire.printSub (toSsa sub)))

private def moves : Bil.Program → List Def
  | [] => []
  | .move var value :: rest => ⟨0, var, value⟩ :: moves rest
  | _ :: rest => moves rest

private def ssaFastPath : IO Unit := do
  sameSsa "a loop" entryLoop
  sameSsa "versioned input" versionedInput
  sameSsa "computed input" computedInput
  sameSsa "existing phis" existingPhi
  sameSsa "siblings" siblings
  sameSsa "SSA again" (toSsa sample)
  let sameTids : Sub := ⟨1, "same", [], [
    ⟨1, [], [⟨1, x, .var y⟩], [⟨2, some (.var y), .goto (.direct 2)⟩, ⟨3, none, .goto (.direct 3)⟩]⟩,
    ⟨2, [], [⟨4, x, .var x⟩], [⟨5, none, .goto (.direct 3)⟩]⟩,
    ⟨3, [], [⟨6, y, .var x⟩], []⟩,
    ⟨3, [], [⟨7, x, .var y⟩], []⟩]⟩
  sameSsa "blocks with the same tid" sameTids
  let path := "/bin/ls"
  if ← System.FilePath.pathExists path then
    let image ← Image.load path
    match image.sections.find? (·.name == ".text") with
    | none => pure ()
    | some text =>
      let data := image.data.extract text.offset (text.offset + min text.size 4000)
      let disasm ← Disasm.Linear.sweep (← Target.X86.disassembler text.addr) data text.addr
      let flag : Var := ⟨"ZF", .imm 1, 0, false⟩
      let blks : List Blk := disasm.blocks.map fun block =>
        let successors := (block.instructions.getLast?.map (·.successors)).getD []
        { tid := block.start, defs := block.instructions.flatMap fun insn => moves insn.bil,
          jmps := successors.map fun next => ⟨next, some (.var flag), .goto (.direct next)⟩ }
      let entry : Blk := { tid := 7, jmps := blks.map fun blk => ⟨blk.tid, some (.var flag), .goto (.direct blk.tid)⟩ }
      sameSsa "real code" ⟨1, "real", [], entry :: blks⟩

def run : IO Unit := do
  ssaFastPath
  regressions
  match (toSsa siblings).block 3 with
  | some block =>
    match block.defs with
    | [read] => assertEqual "sibling definitions are out of scope" (expString (.var x)) (expString read.rhs)
    | _ => throw <| IO.userError "missing sibling definition"
  | none => throw <| IO.userError "missing sibling block"
  let connected := Cfg.connected sample
  assertEqual "connected CFG pseudo entry" pseudoStart connected.start
  assertTrue "connected CFG includes disconnected component" (connected.reachable.contains 99)
  assertTrue "disconnected component linked from pseudo entry" ((connected.predecessors 99).contains pseudoStart)
  assertTrue "disconnected component linked to pseudo exit" ((connected.successors 99).contains pseudoExit)
  let ssa := toSsa sample
  assertEqual "SSA preserves block order" [1, 2, 3, 4, 99] (ssa.blks.map Blk.tid)
  assertTrue "SSA removes pseudo blocks" (!(ssa.blks.map Blk.tid).contains pseudoStart)
  match ssa.block 4 with
  | none => throw <| IO.userError "missing SSA join"
  | some join =>
    assertEqual "one phi at diamond join" 1 join.phis.length
    match join.phis with
    | [phi] =>
      assertEqual "phi receives fresh version" 4 phi.var.index
      match Assoc.get 2 phi.values, Assoc.get 3 phi.values with
      | some left, some right =>
        assertEqual "left phi input version" (expString (.var (x.version 2))) (expString left)
        assertEqual "right phi input version" (expString (.var (x.version 3))) (expString right)
      | _, _ => throw <| IO.userError "missing phi inputs"
    | _ => pure ()
    match join.defs with
    | [defn] =>
      assertEqual "join definition uses phi version" (expString (.var (x.version 4))) (expString defn.rhs)
    | _ => throw <| IO.userError "missing join definition"
  match ssa.block 99 with
  | some block =>
    match block.defs with
    | [defn] => assertEqual "disconnected definition renamed" 5 defn.var.index
    | _ => throw <| IO.userError "missing disconnected definition"
  | none => throw <| IO.userError "disconnected block removed"
  let definitions := ssa.blks.flatMap Blk.definedVars
  assertEqual "SSA definitions are unique" definitions.length definitions.eraseDups.length
  let empty : Sub := ⟨1, "empty", [], []⟩
  assertEqual "empty subroutine SSA" 0 (toSsa empty).blks.length
  -- pruned SSA: `x` is assigned in both arms and read by no one after the join
  let deadJoin : Sub := ⟨1, "dead-join", [], [
    ⟨1, [], [], [goto 1 2, goto 2 3]⟩,
    ⟨2, [], [defn 2 x (int 1)], [goto 3 4]⟩,
    ⟨3, [], [defn 3 x (int 2)], [goto 4 4]⟩,
    ⟨4, [], [defn 4 y (int 3)], [⟨5, none, .goto (.indirect (.var y))⟩]⟩]⟩
  let phisOf (sub : Sub) : Nat := (sub.blks.map (·.phis.length)).sum
  assertTrue "minimal SSA has a phi at the join" (phisOf (toSsa deadJoin) > 0)
  assertEqual "pruned SSA has no phi nothing reads" 0 (phisOf (toSsaPruned deadJoin))
  let liveJoin : Sub := ⟨1, "live-join", [], [
    ⟨1, [], [], [goto 1 2, goto 2 3]⟩,
    ⟨2, [], [defn 2 x (int 1)], [goto 3 4]⟩,
    ⟨3, [], [defn 3 x (int 2)], [goto 4 4]⟩,
    ⟨4, [], [], [⟨5, none, .goto (.indirect (.var x))⟩]⟩]⟩
  assertEqual "pruned SSA keeps a phi that is read" 1 (phisOf (toSsaPruned liveJoin))
  assertEqual "a protected output keeps its phi" 1 (phisOf (toSsaPruned deadJoin [x]))
  -- arguments run on entry, where every variable reads itself
  let withArgs : Sub := { deadJoin with args := [defn 7 y (.var x)] }
  assertEqual "SSA leaves arguments as they are" (withArgs.args.map (expString ·.rhs)) ((toSsa withArgs).args.map (expString ·.rhs))

end Bap.Tests.Ssa
