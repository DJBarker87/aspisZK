import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op82Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op82
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op82Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op82_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (PV_Join_Wire_Selection.selected base ops).op82 = .ok PV_CB_ShippedOp82.aspis_core.r0.merkle.C1_TAG := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_CB_Op82Source.op82_source ops
#print op82_source
#print axioms op82_source
end R1Z.PV_Join_Wire_Op82
