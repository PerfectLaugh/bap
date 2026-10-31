import BapTests.Support

namespace Bap.Tests.Disasm

open Bap
open Bap.Disasm

private def bytes (values : List Nat) : ByteArray := ByteArray.mk (values.map UInt8.ofNat).toArray

private def decodeWith (disassembler : Disassembler) (values : List Nat) : IO Insn := do
  match ← disassembler.decode 0 (bytes values) with
  | .ok insn => pure insn
  | .error error => throw <| IO.userError error

private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩

private def executeEffect (insn : Insn) (env : Bil.Env := []) : IO (Bil.State × Bil.Effect) :=
  match Bil.run insn.bil { env := env } with
  | .ok result => pure result
  | .error error => throw <| IO.userError error

private def execute (insn : Insn) (env : Bil.Env := []) : IO Bil.State := do
  let (state, _) ← executeEffect insn env
  pure state

private def assertJump (label : String) (expected : Nat) : Bil.Effect → IO Unit
  | .jump target => assertEqual label expected target.toNat
  | _ => throw <| IO.userError s!"{label}: expected jump effect"

private def assertReg (label name : String) (expected : Nat) (state : Bil.State) : IO Unit :=
  match Bil.lookup state.env (reg name) with
  | .ok (.bits value) => assertEqual label expected value.toNat
  | .ok _ => throw <| IO.userError s!"{name} is not a bitvector"
  | .error error => throw <| IO.userError error

private def assertFlag (label name : String) (expected : Nat) (state : Bil.State) : IO Unit :=
  let var : Bap.Var := ⟨name, .imm 1, 0, false⟩
  match Bil.lookup state.env var with
  | .ok (.bits value) => assertEqual label expected value.toNat
  | .ok _ => throw <| IO.userError s!"{name} is not a bit"
  | .error error => throw <| IO.userError error

private def assertNormal (label : String) : Bil.Effect → IO Unit
  | .normal => IO.println s!"ok: {label}"
  | _ => throw <| IO.userError s!"{label}: expected normal effect"

private def memVar : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩

private def assertMemory (label : String) (address expected : Nat) (state : Bil.State) : IO Unit :=
  match Bil.lookup state.env memVar with
  | .ok (@Value.memory 64 memory) =>
    assertEqual label expected (Memory.read memory (BitVec.ofNat 64 address) .little 8).toNat
  | .ok _ => throw <| IO.userError "memory is not mapped"
  | .error error => throw <| IO.userError error

def run : IO Unit := do
  let decode := decodeWith (← Target.X86.disassembler 0)
  let sub ← decode [0x48, 0x83, 0xec, 0x08]
  assertEqual "x86 stack subtraction assembly" "sub rsp, 0x8" sub.asm
  assertEqual "x86 stack subtraction size" 4 sub.size
  assertTrue "x86 stack subtraction BIL" (!sub.bil.isEmpty)
  let subState ← execute sub [(reg "RSP", .bits (BitVec.ofNat 64 16))]
  assertReg "x86 stack subtraction result" "RSP" 8 subState
  let mov ← decode [0x49, 0x89, 0xd1]
  assertEqual "x86 REX register move" "mov r9, rdx" mov.asm
  let movState ← execute mov [(reg "RDX", .bits (BitVec.ofNat 64 0x1234))]
  assertReg "x86 register move BIL" "R9" 0x1234 movState
  let immediate ← decode [0xb8, 0xff, 0xff, 0xff, 0xff]
  let immediateState ← execute immediate
  assertReg "x86 32-bit write zero extension" "RAX" 0xffffffff immediateState
  let add ← decode [0x48, 0x83, 0xc0, 0xff]
  assertTrue "x86 signed immediate assembly" (add.asm.startsWith "add rax,")
  let addState ← execute add [(reg "RAX", .bits (BitVec.ofNat 64 0))]
  assertReg "x86 signed immediate BIL" "RAX" 0xffffffffffffffff addState
  assertFlag "x86 nonzero result clears ZF" "ZF" 0 addState
  assertFlag "x86 addition without carry" "CF" 0 addState
  assertFlag "x86 negative result sets SF" "SF" 1 addState
  assertFlag "x86 addition without overflow" "OF" 0 addState
  assertFlag "x86 even result parity" "PF" 1 addState
  let carry ← decode [0x48, 0x83, 0xc0, 0x01]
  let carryState ← execute carry [(reg "RAX", .bits (BitVec.ofNat 64 0xffffffffffffffff))]
  assertReg "x86 carried addition result" "RAX" 0 carryState
  assertFlag "x86 addition carry" "CF" 1 carryState
  let oddParityState ← execute carry [(reg "RAX", .bits (BitVec.ofNat 64 0))]
  assertFlag "x86 odd result parity" "PF" 0 oddParityState
  let overflowAddState ← execute carry [(reg "RAX", .bits (BitVec.ofNat 64 0x7fffffffffffffff))]
  assertFlag "x86 positive addition overflow" "OF" 1 overflowAddState
  assertFlag "x86 overflow addition sign" "SF" 1 overflowAddState
  let borrow ← decode [0x48, 0x83, 0xe8, 0x01]
  let borrowState ← execute borrow [(reg "RAX", .bits (BitVec.ofNat 64 0))]
  assertReg "x86 subtraction borrow result" "RAX" 0xffffffffffffffff borrowState
  assertFlag "x86 subtraction borrow" "CF" 1 borrowState
  let overflowSubState ← execute borrow [(reg "RAX", .bits (BitVec.ofNat 64 0x8000000000000000))]
  assertFlag "x86 negative subtraction overflow" "OF" 1 overflowSubState
  assertFlag "x86 overflow subtraction sign" "SF" 0 overflowSubState
  let xor ← decode [0x48, 0x31, 0xc0]
  let xorState ← execute xor [(reg "RAX", .bits (BitVec.ofNat 64 0x1234))]
  assertReg "x86 XOR BIL" "RAX" 0 xorState
  assertFlag "x86 zero result sets ZF" "ZF" 1 xorState
  assertFlag "x86 logical operation clears CF" "CF" 0 xorState
  assertFlag "x86 logical operation clears SF" "SF" 0 xorState
  assertFlag "x86 logical operation clears OF" "OF" 0 xorState
  assertFlag "x86 logical zero even parity" "PF" 1 xorState
  let lea ← decode [0x48, 0x8d, 0x05, 0x04, 0, 0, 0]
  let leaState ← execute lea
  assertReg "x86 RIP-relative LEA" "RAX" 11 leaState
  let load ← decode [0x48, 0x8b, 0x05, 0, 0, 0, 0]
  let memory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 7)
    (BitVec.ofNat 64 0x1234) .little 8 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let loadState ← execute load [(⟨"mem", .mem 64 8, 0, false⟩, .memory memory)]
  assertReg "x86 RIP-relative load" "RAX" 0x1234 loadState
  let push ← decode [0x54]
  let pushState ← execute push [(reg "RSP", .bits (BitVec.ofNat 64 0x1000)),
    (memVar, .memory (Memory.empty 64))]
  assertReg "x86 push RSP final stack pointer" "RSP" 0xff8 pushState
  assertMemory "x86 push RSP stores original value" 0xff8 0x1000 pushState
  let stackMemory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 0x1000)
    (BitVec.ofNat 64 0x5678) .little 8 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let pop ← decode [0x5b]
  let popState ← execute pop [(reg "RSP", .bits (BitVec.ofNat 64 0x1000)),
    (memVar, .memory stackMemory)]
  assertReg "x86 pop destination" "RBX" 0x5678 popState
  assertReg "x86 pop stack increment" "RSP" 0x1008 popState
  let popRsp ← decode [0x5c]
  let popRspState ← execute popRsp [(reg "RSP", .bits (BitVec.ofNat 64 0x1000)),
    (memVar, .memory stackMemory)]
  assertReg "x86 pop RSP final value" "RSP" 0x5678 popRspState
  let callInsn ← decode [0xe8, 0, 0, 0, 0]
  let (callState, callEffect) ← executeEffect callInsn [(reg "RSP", .bits (BitVec.ofNat 64 0x1000)),
    (memVar, .memory (Memory.empty 64))]
  assertReg "x86 call stack pointer" "RSP" 0xff8 callState
  assertMemory "x86 call return address" 0xff8 5 callState
  assertJump "x86 call target" 5 callEffect
  let retInsn ← decode [0xc3]
  let (retState, retEffect) ← executeEffect retInsn [(reg "RSP", .bits (BitVec.ofNat 64 0x1000)),
    (memVar, .memory stackMemory)]
  assertReg "x86 return stack pointer" "RSP" 0x1008 retState
  assertJump "x86 return target" 0x5678 retEffect
  let jumpInsn ← decode [0xe9, 0, 0, 0, 0]
  let (_, jumpEffect) ← executeEffect jumpInsn
  assertJump "x86 direct jump target" 5 jumpEffect
  let zf : Bap.Var := ⟨"ZF", .imm 1, 0, false⟩
  let je ← decode [0x74, 0]
  let (_, jeTaken) ← executeEffect je [(zf, .bits (BitVec.ofNat 1 1))]
  assertJump "x86 je taken" 2 jeTaken
  let (_, jeNotTaken) ← executeEffect je [(zf, .bits (BitVec.ofNat 1 0))]
  assertNormal "x86 je not taken" jeNotTaken
  let jne ← decode [0x75, 0]
  let (_, jneTaken) ← executeEffect jne [(zf, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jne taken" 2 jneTaken
  let cf : Bap.Var := ⟨"CF", .imm 1, 0, false⟩
  let jb ← decode [0x72, 0]
  let (_, jbTaken) ← executeEffect jb [(cf, .bits (BitVec.ofNat 1 1))]
  assertJump "x86 jb taken" 2 jbTaken
  let jae ← decode [0x73, 0]
  let (_, jaeTaken) ← executeEffect jae [(cf, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jae taken" 2 jaeTaken
  let jbe ← decode [0x76, 0]
  let (_, jbeTaken) ← executeEffect jbe [(cf, .bits (BitVec.ofNat 1 0)), (zf, .bits (BitVec.ofNat 1 1))]
  assertJump "x86 jbe taken on zero" 2 jbeTaken
  let ja ← decode [0x77, 0]
  let (_, jaNotTaken) ← executeEffect ja [(cf, .bits (BitVec.ofNat 1 0)), (zf, .bits (BitVec.ofNat 1 1))]
  assertNormal "x86 ja not taken on zero" jaNotTaken
  let sf : Bap.Var := ⟨"SF", .imm 1, 0, false⟩
  let of : Bap.Var := ⟨"OF", .imm 1, 0, false⟩
  let jo ← decode [0x70, 0]
  let (_, joTaken) ← executeEffect jo [(of, .bits (BitVec.ofNat 1 1))]
  assertJump "x86 jo taken" 2 joTaken
  let jno ← decode [0x71, 0]
  let (_, jnoTaken) ← executeEffect jno [(of, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jno taken" 2 jnoTaken
  let js ← decode [0x78, 0]
  let (_, jsTaken) ← executeEffect js [(sf, .bits (BitVec.ofNat 1 1))]
  assertJump "x86 js taken" 2 jsTaken
  let jns ← decode [0x79, 0]
  let (_, jnsTaken) ← executeEffect jns [(sf, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jns taken" 2 jnsTaken
  let jl ← decode [0x7c, 0]
  let (_, jlTaken) ← executeEffect jl [(sf, .bits (BitVec.ofNat 1 1)), (of, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jl taken" 2 jlTaken
  let jge ← decode [0x7d, 0]
  let (_, jgeTaken) ← executeEffect jge [(sf, .bits (BitVec.ofNat 1 0)), (of, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jge taken" 2 jgeTaken
  let jle ← decode [0x7e, 0]
  let (_, jleTaken) ← executeEffect jle [(zf, .bits (BitVec.ofNat 1 1)),
    (sf, .bits (BitVec.ofNat 1 0)), (of, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jle taken on zero" 2 jleTaken
  let jg ← decode [0x7f, 0]
  let (_, jgNotTaken) ← executeEffect jg [(zf, .bits (BitVec.ofNat 1 1)),
    (sf, .bits (BitVec.ofNat 1 0)), (of, .bits (BitVec.ofNat 1 0))]
  assertNormal "x86 jg not taken on zero" jgNotTaken
  let pf : Bap.Var := ⟨"PF", .imm 1, 0, false⟩
  let jp ← decode [0x7a, 0]
  let (_, jpTaken) ← executeEffect jp [(pf, .bits (BitVec.ofNat 1 1))]
  assertJump "x86 jp taken" 2 jpTaken
  let jnp ← decode [0x7b, 0]
  let (_, jnpTaken) ← executeEffect jnp [(pf, .bits (BitVec.ofNat 1 0))]
  assertJump "x86 jnp taken" 2 jnpTaken
  let indirectMemory ← match Memory.write (Memory.empty 64) (BitVec.ofNat 64 6)
    (BitVec.ofNat 64 0x1234) .little 8 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let indirectJump ← decode [0xff, 0x25, 0, 0, 0, 0]
  let (_, indirectJumpEffect) ← executeEffect indirectJump [(memVar, .memory indirectMemory)]
  assertJump "x86 indirect jump target" 0x1234 indirectJumpEffect
  let indirectCall ← decode [0xff, 0x15, 0, 0, 0, 0]
  let (indirectState, indirectEffect) ← executeEffect indirectCall
    [(reg "RSP", .bits (BitVec.ofNat 64 14)), (memVar, .memory indirectMemory)]
  assertReg "x86 indirect call stack pointer" "RSP" 6 indirectState
  assertMemory "x86 indirect call return address" 6 6 indirectState
  assertJump "x86 indirect call preserves target" 0x1234 indirectEffect
  let linear ← Linear.sweep (← Target.X86.disassembler 0) (bytes [0x48, 0x83, 0xec, 0x08, 0xc3])
  assertEqual "linear sweep instruction count" 2 linear.instructions.length
  assertEqual "linear sweep has no errors" [] linear.errors
  -- revisiting addresses costs no fuel, and running out of it is an error
  let loopInsn (address : Nat) (flow : Flow) (target : Nat) : Insn :=
    { address := address, size := 1, asm := "", flow := flow, target := some target }
  let loopDecoder : Disassembler := { name := "loop", decode := fun address _ => pure <| .ok <|
    match address with
    | 0 => loopInsn 0 .conditionalJump 3
    | 1 => loopInsn 1 .conditionalJump 1
    | 2 => loopInsn 2 .jump 1
    | address => loopInsn address .ret 0 }
  let loop ← Recursive.scan loopDecoder (bytes [0, 0, 0, 0]) 0
  assertEqual "recursive scan reaches past revisited addresses" [0, 1, 2, 3]
    (loop.instructions.map Insn.address)
  assertEqual "recursive scan with fuel left has no errors" [] loop.errors
  let endlessInsn (address : Nat) : Insn := { address := address, size := 1, asm := "" }
  let endless : Disassembler := { name := "endless", decode := fun address _ => pure (.ok (endlessInsn address)) }
  let exhausted ← Recursive.scan endless (bytes [0]) 0
  assertEqual "recursive scan reports running out of fuel" [Recursive.outOfFuel] exhausted.errors
  -- a delay slot is listed and is on the path to the target, without a fall-through edge
  let mips ← Target.MIPS.disassembler 0
  let mipsCode := bytes [0x08, 0, 0, 0x04, 0x24, 0x42, 0, 0x01, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0x03, 0xe0, 0, 0x08, 0x24, 0x63, 0, 0x01]
  let delayed ← Recursive.scan mips mipsCode 0
  assertEqual "scan covers delay slots" [0, 4, 16, 20] (delayed.instructions.map Insn.address)
  assertEqual "scan goes through delay slots" [(0, 4), (4, 16), (16, 20)] delayed.edges
  assertEqual "scan of delay slots has no errors" [] delayed.errors
  -- a slot that is also reached by a branch keeps its own fall-through
  let reached ← Recursive.scan mips (bytes [0x10, 0, 0, 0x01, 0x24, 0x42, 0, 0x01, 0x03, 0xe0, 0, 0x08,
    0x24, 0x63, 0, 0x01]) 0
  assertEqual "scan of an assembler b" [0, 4, 8, 12] (reached.instructions.map Insn.address)
  assertEqual "scan of an assembler b edges" [(0, 4), (4, 8), (8, 12)] reached.edges
  -- a conditional branch runs its slot and decides after it: bne $2, $0, 16 with a nop in the slot, then jr $ra twice
  let beq ← Recursive.scan mips (bytes [0x14, 0x40, 0, 0x03, 0, 0, 0, 0, 0x03, 0xe0, 0, 0x08, 0, 0, 0, 0,
    0x03, 0xe0, 0, 0x08, 0, 0, 0, 0]) 0
  assertEqual "conditional branch goes through its slot, both ways"
    [(0, 4), (4, 8), (4, 16)] (beq.edges.take 3)
  assertEqual "conditional branch has no edge of its own to the target" false (beq.edges.contains (0, 16))
  -- beql: taken it goes through the slot to the target, not taken it skips the slot and nothing leaves it otherwise
  let beql ← Recursive.scan mips (bytes [0x50, 0x40, 0, 0x03, 0x24, 0x42, 0, 0x01, 0x03, 0xe0, 0, 0x08, 0, 0, 0, 0,
    0x03, 0xe0, 0, 0x08, 0, 0, 0, 0]) 0
  assertEqual "likely branch lists its slot" true (beql.instructions.any (·.address == 4))
  assertEqual "likely branch has an edge into its slot" true (beql.edges.contains (0, 4))
  assertEqual "likely branch not taken skips its slot" true (beql.edges.contains (0, 8))
  assertEqual "likely branch taken goes from its slot to the target" true (beql.edges.contains (4, 16))
  assertEqual "likely branch has no edge from its slot past it" false (beql.edges.contains (4, 8))
  assertEqual "likely branch has no edge of its own to the target" false (beql.edges.contains (0, 16))
  assertEqual "likely branch scan has no errors" [] beql.errors
  -- bltzall $2, 16: a likely call, taken it goes through the slot and comes back after it, not taken it skips the slot
  let bltzall ← Recursive.scan mips (bytes [0x04, 0x52, 0, 0x03, 0x24, 0x42, 0, 0x01, 0x03, 0xe0, 0, 0x08, 0, 0, 0, 0,
    0x03, 0xe0, 0, 0x08, 0, 0, 0, 0]) 0
  assertEqual "likely call is a call" (some Disasm.Flow.call) ((bltzall.instructions.find? (·.address == 0)).map (·.flow))
  assertEqual "likely call lists its slot" true (bltzall.instructions.any (·.address == 4))
  assertEqual "likely call has an edge into its slot" true (bltzall.edges.contains (0, 4))
  assertEqual "likely call not taken skips its slot" true (bltzall.edges.contains (0, 8))
  assertEqual "likely call goes on from its slot past it" true (bltzall.edges.contains (4, 8))
  assertEqual "likely call scan has no errors" [] bltzall.errors
  -- bgezall $2, 16 the same
  let bgezall ← Recursive.scan mips (bytes [0x04, 0x53, 0, 0x03, 0x24, 0x42, 0, 0x01, 0x03, 0xe0, 0, 0x08, 0, 0, 0, 0]) 0
  assertEqual "the other likely call skips its slot" true (bgezall.edges.contains (0, 8))
  let slotTwice : Disassembler := {
    name := "slot", decode := fun address _ => pure <| .ok <|
      match address with
      | 0 => { address := 0, size := 1, asm := "", flow := .jump, target := some 3 }
      | 3 => { address := 3, size := 1, asm := "", flow := .jump, target := some 1 }
      | 1 => { address := 1, size := 1, asm := "", flow := .normal }
      | address => { address := address, size := 1, asm := "", flow := .ret }
    hasDelaySlot := fun insn => insn.address == 0 }
  let twice ← Recursive.scan slotTwice (bytes [0, 0, 0, 0]) 0
  assertEqual "a slot reached twice is listed once" [0, 1, 3, 2]
    (twice.instructions.map Insn.address)
  assertEqual "a slot reached on its own falls through" [(0, 1), (1, 3), (3, 1), (1, 2)] twice.edges
  let branch ← Recursive.scan (← Target.X86.disassembler 0) (bytes [0xeb, 0x02, 0xc3, 0x90, 0xc3]) 0
  assertEqual "recursive branch skips unreachable" [0, 4] (branch.instructions.map Insn.address)
  assertEqual "recursive branch edges" [(0, 4)] branch.edges
  let conditional ← Recursive.scan (← Target.X86.disassembler 0) (bytes [0x70, 0x02, 0xc3, 0x90, 0xc3]) 0
  assertEqual "conditional branch visits both successors" [0, 2, 4] (conditional.instructions.map Insn.address)
  let call ← Recursive.scan (← Target.X86.disassembler 0) (bytes [0xe8, 0, 0, 0, 0, 0xc3]) 0
  assertEqual "call continues to return block" [0, 5] (call.instructions.map Insn.address)
  let called ← Recursive.scan (← Target.X86.disassembler 0) (bytes [0xe8, 0x01, 0, 0, 0, 0xc3, 0xc3]) 0
  assertEqual "a scan follows a direct call" [0, 5, 6] (called.instructions.map Insn.address |>.mergeSort)
  assertEqual "a call is no edge of the flow" [(0, 5)] called.edges
  let rooted ← Recursive.scanRoots (← Target.X86.disassembler 0) (bytes [0xc3, 0x90, 0xc3]) 3 0 [0, 1]
  assertEqual "a scan goes from all its roots" [0, 1, 2] (rooted.instructions.map Insn.address)
  let single ← Recursive.scan (← Target.X86.disassembler 0) (bytes [0xc3, 0x90, 0xc3]) 0
  assertEqual "a scan from one root finds what it reaches" [0] (single.instructions.map Insn.address)
  -- `jmp` from one region to another, and from there to neither
  let first : Image.MemRegion := { addr := 0x1000, data := bytes [0xe9, 0xfb, 0x0f, 0, 0], executable := true }
  let second : Image.MemRegion := { addr := 0x2000, data := bytes [0xe9, 0xfb, 0x2f, 0, 0], executable := true }
  let both := Disassembler.ofRegions (← Target.X86.disassembler 0)
    [(first, ← Target.X86.disassembler 0x1000), (second, ← Target.X86.disassembler 0x2000)]
  let across ← Recursive.scanRoots both ByteArray.empty 10 0x1000 [0x1000]
  assertEqual "a scan crosses regions" [0x1000, 0x2000] (across.instructions.map Insn.address)
  assertEqual "an address of no region is an error" ["20480 is not in code"] (across.errors)
  let x86 ← Target.X86.disassembler 0
  -- 0x06 doesn't decode in 64-bit mode; the sweep goes on at the next multiple of 4
  let swept ← Recursive.scanRegions (Disassembler.ofRegions x86 [({ addr := 0, data := bytes [0xc3, 0x06, 0x06, 0x06, 0x90, 0xc3] }, x86)])
    6 0 [0] { resume := (· % 4 == 0) } [(0, 6)]
  assertEqual "a sweep finds what the scan doesn't and steps over what doesn't decode" [0, 4, 5] (swept.instructions.map Insn.address)
  assertEqual "a sweep has no errors of its own" [] swept.errors
  let plain ← Recursive.scanRegions (Disassembler.ofRegions x86 [({ addr := 0, data := bytes [0xc3, 0x06, 0x06, 0x06, 0x90, 0xc3] }, x86)])
    6 0 [0] {} []
  assertEqual "without ranges there is no sweep" [0] (plain.instructions.map Insn.address)
  let host ← Image.Elf.load "/bin/echo"
  match host.memory.entries.find? fun entry => entry.1.contains host.entryPoint with
  | none => throw <| IO.userError "host entry is unmapped"
  | some (region, _) =>
    let disasm ← Recursive.scan (← Target.X86.disassembler region.addr) region.data host.entryPoint
    assertEqual "host disassembly has no errors" [] disasm.errors
    assertEqual "host entry instruction count" 13 disasm.instructions.length
    assertEqual "host entry basic blocks" 2 disasm.blocks.length
    assertEqual "host entry ends with barrier" (some Flow.barrier) (disasm.instructions.getLast?.map Insn.flow)

end Bap.Tests.Disasm
