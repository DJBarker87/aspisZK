import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op105Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op105
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op105Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op105_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.M31),
    (PV_Join_Wire_Selection.selected base ops).op105 x =
      PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op105Exact.op105_source ops x
#print op105_source
#print axioms op105_source
end R1Z.PV_Join_Wire_Op105
