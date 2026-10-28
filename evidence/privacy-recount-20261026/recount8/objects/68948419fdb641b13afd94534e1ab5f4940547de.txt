import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op84Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op84
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op84Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op84_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (tag : U8) (values : Slice U8),
    (PV_Join_Wire_Selection.selected base ops).op84 hash tag values =
      PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro hash tag values
  exact R1Z.PV_CB_Op84Exact.op84_source ops hash tag values
#print op84_source
#print axioms op84_source
end R1Z.PV_Join_Wire_Op84
