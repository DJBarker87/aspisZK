import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op71Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op71
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op71Transport PV_CB_Op71Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op71_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (bytes : Slice U8),
    (PV_Join_Wire_Selection.selected base ops).op71 bytes = (do
      let value ← PV_CB_ShippedOp71.aspis_core.field.QM31.from_le_bytes bytes
      ok (value.map decode)) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro bytes
  exact R1Z.PV_CB_Op71Exact.op71_source ops bytes
#print op71_source
#print axioms op71_source
end R1Z.PV_Join_Wire_Op71
