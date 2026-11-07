import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S041
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 41: box_lane; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (laneBytes : Slice U8)
 (lane : Box Lane)
 (next : Box Lane → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.lane laneBytes)) next) ()) =
 tryThen (ops.op50 laneBytes) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.lane,value⟩) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.boxed ops owners _ _ _ next
#print axioms step
end NMX_S041
end
