import R1Z.PV_Join_Wire_Op111
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry111
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op111Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.U64 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp111.aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op111 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op111.op111_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry111
