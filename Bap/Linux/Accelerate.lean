import Bap.Linux.Library
import Bap.Crypto.Sha512

/-! # Routines that the host does in place of a guest's own

What takes a guest long and the host little, such as a hash over all of a file, can be done by the host instead, at the routine's own
address, as `Machine.replaceFunction` does. That is only right if the host does what the guest's routine does, which `Machine.accelerate`
checks before it puts the host's in place: on each sample of the accelerator, the routine runs in the guest and the host's function on the
same machine, from the same state, and what they give back and what they leave in memory have to be the same.

What was checked is kept by the name of the accelerator and the digest of the routine's code, for as long as the host runs: another process,
or another machine, with the same code puts the host's in place without running the guest's again. `trusted` and `trust` carry that from
one run of the host to another. -/

namespace Bap.Linux

namespace Accelerate

/-- One input to check an accelerator on: what it puts in the machine, which gives the arguments of the call, and where in memory, of those
arguments, what the call leaves is to be the same. -/
structure Sample where
  prepare : Machine → IO (List Nat)
  outputs : List Nat → List (Nat × Nat) := fun _ => []

/-- What the host does in place of a routine, and what it is checked on. -/
structure Accelerator where
  name : String
  host : HostFunction
  samples : List Sample
  /-- Whether what the call gives back is to be the same, which it isn't of a routine that gives nothing. -/
  compareResult : Bool := true

/-- What `Machine.accelerate` did. -/
inductive Outcome where
  /-- It checked the host's against the routine, which were the same, and put the host's in place. -/
  | validated (hook : Bap.Emu.HookId)
  /-- The same code was checked before, so that it put the host's in place without checking again. -/
  | reused (hook : Bap.Emu.HookId)
  /-- They weren't the same, on this sample, as this says, and the routine is as it was. -/
  | rejected (sample : Nat) (why : String)
  deriving Repr

/-- What was found the same, by the name of the accelerator and the digest of the code. -/
initialize validated : IO.Ref (Std.HashSet (String × Nat)) ← IO.mkRef {}

/-- What was found the same so far, to `trust` in another run of the host. -/
def trusted : IO (List (String × Nat)) := do pure (← validated.get).toList

/-- Takes these as found the same, as `trusted` gave them. -/
def trust (entries : List (String × Nat)) : IO Unit :=
  validated.modify fun set => entries.foldl (·.insert ·) set

end Accelerate

open Accelerate in
/-- How the routine at `address` and the host's function differ on a sample, if they do: each runs from the same state, which the
machine is in again after. -/
private def differenceOn (machine : Machine) (address : Nat) (accelerator : Accelerator) (sample : Sample) : IO (Option String) := do
  let saved ← machine.save
  let width := machine.architecture.bits
  let outcome ← try
      let arguments ← sample.prepare machine
      let guestResult := (← machine.call address arguments) % 2 ^ width
      let guestOutputs ← (sample.outputs arguments).mapM fun (at_, size) => machine.read at_ size
      machine.restore saved
      let arguments ← sample.prepare machine
      let hostResult := (← accelerator.host machine arguments) % 2 ^ width
      let hostOutputs ← (sample.outputs arguments).mapM fun (at_, size) => machine.read at_ size
      if accelerator.compareResult && guestResult != hostResult then
        pure (some s!"the routine gives {guestResult} and the host {hostResult}")
      else
        match ((sample.outputs arguments).zip (guestOutputs.zip hostOutputs)).find? fun (_, guest, host) => guest != host with
        | some ((at_, _), guest, host) => pure (some s!"at {at_} the routine leaves {guest.toList} and the host {host.toList}")
        | none => pure none
    catch error => pure (some s!"it can't be run: {error}")
  machine.restore saved
  pure outcome

open Accelerate in
/-- Puts what the host does in place of the routine at `address`, of `size` bytes of code, once it is found to do the same on each
sample of the accelerator, or at once if the same code was found so before: see `Bap.Linux.Accelerate`. The machine is as it was
after checking, and the routine is as it was if they differ. -/
def Machine.accelerate (machine : Machine) (accelerator : Accelerator) (address size : Nat) : IO Outcome := do
  let code ← machine.read address size
  let key := (accelerator.name, (Wire.digest code).toNat)
  let install : IO Bap.Emu.HookId := machine.replaceFunction address accelerator.host s!"accelerated {accelerator.name}"
  if (← validated.get).contains key then return Outcome.reused (← install)
  for (sample, index) in accelerator.samples.zipIdx do
    if let some why := ← differenceOn machine address accelerator sample then return Outcome.rejected index why
  validated.modify (·.insert key)
  pure (Outcome.validated (← install))

namespace Accelerate

/-- SHA-512 of a routine that takes the data, its length, and where the 64 bytes of the hash go, as `SHA512` of OpenSSL does, which
gives back where they went when `returnsOutput`. It is checked on each of `inputs`. -/
def sha512 (inputs : List ByteArray := [ByteArray.empty, "abc".toUTF8, ByteArray.mk ((Array.range 300).map (·.toUInt8))])
    (returnsOutput : Bool := false) : Accelerator where
  name := "sha512"
  host := fun machine arguments => do
    let output := arguments.getD 2 0
    machine.write output (Bap.Crypto.Sha512.hash (← machine.read (arguments.getD 0 0) (arguments.getD 1 0)))
    pure (if returnsOutput then output else 0)
  compareResult := returnsOutput
  samples := inputs.map fun input => {
    prepare := fun machine => do
      let data ← machine.malloc (max 1 input.size)
      machine.write data input
      let output ← machine.malloc 64
      pure [data, input.size, output]
    outputs := fun arguments => [(arguments.getD 2 0, 64)] }

end Accelerate

end Bap.Linux
