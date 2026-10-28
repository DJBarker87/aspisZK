import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op118Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op118
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op118Transport PV_CB_Op118Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op118_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : Array aspis_core.field.QM31 10#usize),
    (PV_Join_Wire_Selection.selected base ops).op118 x = (do
      let value ← PV_CB_ShippedOp118.aspis_core.state_only_prefix.r0.statement_points (encodeArray x)
      ok (decodePoints value)) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op118Exact.op118_source ops x
#print op118_source
#print axioms op118_source
end R1Z.PV_Join_Wire_Op118
