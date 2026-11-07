import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S026
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 26: check; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (wrongMasterPda : Bool)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.check wrongMasterPda) next) ()) =
 if wrongMasterPda then ok (.Err .InvalidAccountData) else NMX_ValueLink.erase (eval (source ops owners) (next ()) ()) := by
 cases h : (wrongMasterPda) <;> simp [NMX_SourceProgram.check,h,NMX_Program.bind,eval,NMX_ValueLink.erase]
#print axioms step
end NMX_S026
end
