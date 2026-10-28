import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB3_Op120Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op120
open Aeneas Aeneas.Std Result  ProverRwFull Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op120Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op120_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (p : Array aspis_core.field.QM31 28#usize),
    (PV_Join_Wire_Selection.selected base ops).op120 p = Raw.boundary_flat p := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro p
  exact R1Z.PV_CB3_Op120Source.op120_source ops p
#print op120_source
#print axioms op120_source
end R1Z.PV_Join_Wire_Op120
