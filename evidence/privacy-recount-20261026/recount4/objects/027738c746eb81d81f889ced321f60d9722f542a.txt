import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op83Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op83
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op83Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op83_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    (PV_Join_Wire_Selection.selected base ops).op83 = .ok PV_CB_ShippedOp83.aspis_core.r0.merkle.C2_TAG := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  exact R1Z.PV_CB_Op83Source.op83_source ops
#print op83_source
#print axioms op83_source
end R1Z.PV_Join_Wire_Op83
