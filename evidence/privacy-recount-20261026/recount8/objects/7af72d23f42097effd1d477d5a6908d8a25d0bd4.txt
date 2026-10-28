import R1Z.PV_Join_Wire_Op101
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry101
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op101Transport PV_CB_Op101Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.QM31 → Result aspis_core.field.QM31 :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => (do
      let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg (encode x)
      ok (decode y))
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op101 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op101.op101_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry101
