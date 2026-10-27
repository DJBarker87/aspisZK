import R1Z.PV_Join_Wire_Op83
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry83
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op83Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.U8 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp83.aspis_core.r0.merkle.C2_TAG
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op83 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op83.op83_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry83
