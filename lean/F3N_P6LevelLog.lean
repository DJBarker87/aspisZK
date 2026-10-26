import F3N_PhysicalLevels
import MultiproofConeP6Callbacks
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_P6LevelLog
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport

theorem source (height : Nat) (s : reference.Scratch) (physical : Slice U8) :
    SdkC_Oracle.program (Port9OR_P6Levels.levels height s physical)=
      transport (MultiproofConePhysicalLevels.levels height s physical) := by
  rw [← F3N_PhysicalCode.transport,F3N_PhysicalLevels.levels]

theorem callbacks {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (law : ∀ input,D.digest hash input=ok (rawOracle H input))
    (occupied sibling : MultiproofConeP6Callbacks.Parent)
    (og : MultiproofConeP6Callbacks.ParentGate (rawOracle H) occupied)
    (sg : MultiproofConeP6Callbacks.ParentGate (rawOracle H) sibling)
    (height : Nat) (s : reference.Scratch) (physical : Slice U8)
    (size : physical.val.length≤5504) (domain : MultiproofConeLevelIteration.Domain physical s) :
    eval H (SdkC_Oracle.program (Port9OR_P6Levels.levels height s physical))=
      eval H (transport (MultiproofConeP6Composition.levels
        (MultiproofConeP6Callbacks.nodeWith occupied sibling) height s physical)) := by
  rw [source,transport_observation,transport_observation]
  rw [MultiproofConeP6Composition.levels_eq D hash (rawOracle H) law
    (MultiproofConeP6Callbacks.nodeWith occupied sibling)
    (MultiproofConeP6Callbacks.node_gate (rawOracle H) occupied sibling og sg)
    physical size height s domain]

#print axioms source
#print axioms callbacks
end AspisR1.F3N_P6LevelLog
end
