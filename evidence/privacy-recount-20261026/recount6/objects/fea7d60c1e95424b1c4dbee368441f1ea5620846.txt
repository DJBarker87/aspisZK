import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op101Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op101
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op101Transport PV_CB_Op101Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op101_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.QM31),
    (PV_Join_Wire_Selection.selected base ops).op101 x = (do
      let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg (encode x)
      ok (decode y)) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op101Exact.op101_source ops x
#print op101_source
#print axioms op101_source
end R1Z.PV_Join_Wire_Op101
