import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S039
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 39: check; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (wrongCheckpointPda : Bool)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.check wrongCheckpointPda) next) ()) =
 if wrongCheckpointPda then ok (.Err .InvalidAccountData) else NMX_ValueLink.erase (eval (source ops owners) (next ()) ()) := by
 cases h : (wrongCheckpointPda) <;> simp [NMX_SourceProgram.check,h,NMX_Program.bind,eval,NMX_ValueLink.erase]
#print axioms step
end NMX_S039
end
