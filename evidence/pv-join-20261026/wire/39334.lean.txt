import R1Z.PV_Join_Wire_Op105
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry105
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op105Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.M31 → Result (Option aspis_core.field.M31) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv x
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op105 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op105.op105_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry105
