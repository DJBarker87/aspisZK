import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op111Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op111
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op111Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op111_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (PV_Join_Wire_Selection.selected base ops).op111 = .ok PV_CB_ShippedOp111.aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_CB_Op111Source.op111_source ops
#print op111_source
#print axioms op111_source
end R1Z.PV_Join_Wire_Op111
