import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op86Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op86
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op86Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op86_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (PV_Join_Wire_Selection.selected base ops).op86 = .ok PV_CB_ShippedOp86.aspis_core.r0.opening.LANES := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_CB_Op86Source.op86_source ops
#print op86_source
#print axioms op86_source
end R1Z.PV_Join_Wire_Op86
