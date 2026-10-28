import R1Z.PV_RunJoin_PolyCanonical40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_HighCell41
open Aeneas Aeneas.Std ProverRwFull
open PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38
variable [ExternalTypes]

theorem high (q : Q) : PV_RunJoin_HighDomain40.HighZero (cell q) := by
  simpa only [payload,List.append_nil] using PV_RunJoin_PolyCanonical40.high (fun _ => q) 0 1
#print axioms high
end R1Z.PV_RunJoin_HighCell41
