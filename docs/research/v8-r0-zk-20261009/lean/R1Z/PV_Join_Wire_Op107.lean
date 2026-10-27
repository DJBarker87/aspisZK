import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op107Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op107
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op107Transport PV_CB_Op107Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op107_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.QM31),
    (PV_Join_Wire_Selection.selected base ops).op107 x = (do
      let value ← PV_CB_ShippedOp107.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv (encode x)
      ok (value.map decode)) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op107Exact.op107_source ops x
#print op107_source
#print axioms op107_source
end R1Z.PV_Join_Wire_Op107
