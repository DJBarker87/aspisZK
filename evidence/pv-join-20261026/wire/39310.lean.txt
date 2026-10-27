import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op100Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op100
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op100Transport PV_CB_Op100Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op100_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.wide_exact.WideExact),
    (PV_Join_Wire_Selection.selected base ops).op100 x = (do
      let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg (encodeW x)
      ok (decodeW y)) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op100Exact.op100_source ops x
#print op100_source
#print axioms op100_source
end R1Z.PV_Join_Wire_Op100
