import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op72Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op72
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op72Transport PV_CB_Op72Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op72_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.QM31) (bytes : Slice U8),
    (PV_Join_Wire_Selection.selected base ops).op72 x bytes =
      PV_CB_ShippedOp72.aspis_core.field.QM31.write_le_bytes (encode x) bytes := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x bytes
  exact R1Z.PV_CB_Op72Exact.op72_source ops x bytes
#print op72_source
#print axioms op72_source
end R1Z.PV_Join_Wire_Op72
