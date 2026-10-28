import R1Z.PV_RDCD_Audit
set_option autoImplicit false
namespace R1Z.PV_RDCD_Replay
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
noncomputable def v221 := @PV_RDCD_Audit.v221
noncomputable def v222 := @PV_RDCD_Audit.v222
noncomputable def consumed_drop := @PV_RDCD_Audit.consumed_drop
#print axioms v221
#print axioms v222
#print axioms consumed_drop
end R1Z.PV_RDCD_Replay
