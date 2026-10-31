namespace Bap.Tests

inductive Subsystem where
  | core
  | bil
  | bir
  | theory
  | knowledge
  | graphs
  | images
  | disassembly
  | targets
  | primus
  | analyses
  | plugins
  | cli
  deriving DecidableEq, Repr

def allSubsystems : List Subsystem :=
  [.core, .bil, .bir, .theory, .knowledge, .graphs, .images, .disassembly,
    .targets, .primus, .analyses, .plugins, .cli]

structure ParityStatus where
  subsystem : Subsystem
  implemented : Bool
  differentialFixtures : Nat
  deriving Repr

def initialParity : List ParityStatus :=
  allSubsystems.map fun subsystem => ⟨subsystem, false, 0⟩

theorem initialParityCoversEverySubsystem :
    initialParity.map ParityStatus.subsystem = allSubsystems := by
  simp [initialParity, allSubsystems]

theorem initialParityDoesNotClaimCompletion :
    initialParity.all (fun status => !status.implemented) = true := by
  decide

end Bap.Tests
