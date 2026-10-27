import R1Z.PV_Join_Wire_Op107
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry107
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op107Transport PV_CB_Op107Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_core.field.QM31 → Result (Option aspis_core.field.QM31) :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun x => (do
      let value ← PV_CB_ShippedOp107.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv (encode x)
      ok (value.map decode))
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op107 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext x
  exact R1Z.PV_Join_Wire_Op107.op107_source base ops x
#print axioms equation
end R1Z.PV_Join_Wire_Entry107
