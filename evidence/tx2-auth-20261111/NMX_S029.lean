import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S029
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 29: box_checkpoint; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (checkpointBytes : Slice U8)
 (checkpoint : Box Checkpoint)
 (next : Box Checkpoint → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.checkpoint checkpointBytes)) next) ()) =
 tryThen (ops.op49 checkpointBytes) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.checkpoint,value⟩) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.boxed ops owners _ _ _ next
#print axioms step
end NMX_S029
end
