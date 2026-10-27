import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op110Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op110
open Aeneas Aeneas.Std Result  Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op110Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op110_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.M31),
    (PV_Join_Wire_Selection.selected base ops).op110 x =
      PV_CB_ShippedOp110.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB_Op110Source.op110_source ops x
#print op110_source
#print axioms op110_source
end R1Z.PV_Join_Wire_Op110
