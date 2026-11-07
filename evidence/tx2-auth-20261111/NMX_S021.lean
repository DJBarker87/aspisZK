import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S021
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 21: check; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (allLanes : U8)
 (master : Box Master)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.check (master.payload.initialized_lane_mask != allLanes)) next) ()) =
 if (master.payload.initialized_lane_mask != allLanes) then ok (.Err .InvalidAccountData) else NMX_ValueLink.erase (eval (source ops owners) (next ()) ()) := by
 by_cases h : ((master.payload.initialized_lane_mask != allLanes)) = true <;> simp only [NMX_SourceProgram.check,h,↓reduceIte,NMX_Program.bind,eval,NMX_ValueLink.erase]
#print axioms step
end NMX_S021
end
