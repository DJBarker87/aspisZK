import R1Z.PV_Join_Wire_Op82
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry82
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op82Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    Result Std.U8 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  .ok PV_CB_ShippedOp82.aspis_core.r0.merkle.C1_TAG
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op82 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_Join_Wire_Op82.op82_source base ops
#print axioms equation
end R1Z.PV_Join_Wire_Entry82
