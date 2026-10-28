import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB3_Op51Arbitrary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op51
open Aeneas Aeneas.Std Result ProverRwFull PV_CB3_Op51Arbitrary
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op51_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (x : aspis_core.field.wide_exact.WideExact),
    (PV_Join_Wire_Selection.selected base ops).op51 x = PV_CB3_Op51Source.Raw.wide_bytes_flat x := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro x
  exact R1Z.PV_CB3_Op51Arbitrary.op51_source ops x
#print op51_source
#print axioms op51_source
end R1Z.PV_Join_Wire_Op51
