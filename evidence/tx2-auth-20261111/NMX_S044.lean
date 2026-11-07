import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S044
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 44: check; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (wrongLaneMaster : Bool)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.check wrongLaneMaster) next) ()) =
 if wrongLaneMaster then ok (.Err .InvalidAccountData) else NMX_ValueLink.erase (eval (source ops owners) (next ()) ()) := by
 by_cases h : (wrongLaneMaster) = true <;> simp only [NMX_SourceProgram.check,h,↓reduceIte,NMX_Program.bind,eval,NMX_ValueLink.erase]
#print axioms step
end NMX_S044
end
