import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S045
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 45: check; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (outputLane : U8)
 (lane : Box Lane)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.check (lane.payload.lane_id != outputLane)) next) ()) =
 if (lane.payload.lane_id != outputLane) then ok (.Err .InvalidAccountData) else NMX_ValueLink.erase (eval (source ops owners) (next ()) ()) := by
 by_cases h : ((lane.payload.lane_id != outputLane)) = true <;> simp only [NMX_SourceProgram.check,h,↓reduceIte,NMX_Program.bind,eval,NMX_ValueLink.erase]
#print axioms step
end NMX_S045
end
