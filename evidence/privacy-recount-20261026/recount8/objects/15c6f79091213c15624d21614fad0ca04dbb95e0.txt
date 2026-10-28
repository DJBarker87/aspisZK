import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op109Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op109
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op109Transport PV_CB_Op109Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op109_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.wide_exact.WideExact),
    (PV_Join_Wire_Selection.selected base ops).op109 x = (do
      let value ← PV_CB_ShippedOp109.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv (encodeW x)
      ok (value.map decodeW)) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op109Exact.op109_source ops x
#print op109_source
#print axioms op109_source
end R1Z.PV_Join_Wire_Op109
