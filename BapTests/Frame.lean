import BapTests.Support
import Bap.Analysis.Frame

/-! What `Bap.Analysis.Frame` finds of `testsuite/src/frame.c` of each target: how many arguments each function takes in registers,
which on the stack, whether its callers use what it returns, that it keeps what its convention has it keep, and where its returns
leave the stack pointer, which a `stdcall` function of i686 moves past its arguments. -/

namespace Bap.Tests.Frame

open Bap Bap.Analysis

/-- Of a target, how many of `eight`'s arguments are in registers, where those on the stack are, and where a return leaves the
stack pointer from where it was on entry. -/
private def targets : List (String × Nat × List Nat × Int) :=
  [("x86_64", 6, [8, 16], 8), ("aarch64", 8, [], 0), ("riscv64", 8, [], 0), ("arm", 4, [0, 4, 8, 12], 0),
    ("mips", 4, [16, 20, 24, 28], 0), ("mips64el", 8, [], 0), ("powerpc", 8, [], 0), ("powerpc64le", 8, [], 0)]

private def ofTarget (arch : String) (check : Frame.Signature → Frame.Frame → IO Unit) : IO Unit := do
  let path := s!"testsuite/bin/{arch}-linux-none-frame"
  let project ← Project.Project.load path
  let some image := project.image | throw (IO.userError s!"{path} doesn't load")
  let some partition ← Partition.partition project | throw (IO.userError s!"{path} has no partition")
  let some frames := Frame.frames image partition | throw (IO.userError s!"{path} has no frames")
  let names := ["zero", "one", "three", "eight", "saver"] ++ (if arch == "i686" then ["cleans"] else [])
  for name in names do
    let some signature := frames.signatures.find? (·.name == name) | throw (IO.userError s!"{path} has no {name}")
    let some frame := frames.frameOf signature.entry | throw (IO.userError s!"{path} has no frame of {name}")
    assertTrue s!"{arch} {name} keeps what its convention keeps" signature.conforms
    assertEqual s!"{arch}: what {name} returns is used" (name != "zero") signature.returnsValue
    check signature frame

def run : IO Unit := do
  for (arch, registers, stack, returnDelta) in targets do
    ofTarget arch fun signature frame => do
      let name := signature.name
      let expected := match name with
        | "zero" => 0 | "one" => 1 | "three" => 3 | "saver" => 1 | _ => registers
      assertEqual s!"{arch} {name} takes its arguments in registers" expected signature.registerArguments
      assertEqual s!"{arch} {name} takes its arguments on the stack" (if name == "eight" then stack else []) signature.stackArguments
      assertEqual s!"{arch} {name} returns with the stack pointer where it was" (some returnDelta) frame.returnDelta
  -- of i686, all are on the stack, and `cleans` pops them
  ofTarget "i686" fun signature frame => do
    let name := signature.name
    let count := match name with
      | "zero" => 0 | "one" => 1 | "saver" => 1 | "three" => 3 | "cleans" => 3 | _ => 8
    assertEqual s!"i686 {name} takes no arguments in registers" 0 signature.registerArguments
    assertEqual s!"i686 {name} takes its arguments on the stack" ((List.range count).map (4 * · + 4)) signature.stackArguments
    assertEqual s!"i686 {name} returns past its arguments, if it cleans them"
      (some (if name == "cleans" then 16 else 4)) frame.returnDelta

end Bap.Tests.Frame
