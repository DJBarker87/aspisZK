import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op229Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op229
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op229Transport PV_CB_Op229Source
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op229_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ (a b : PV_CB_Op229Transport.Late base),
    (PV_Join_Wire_Selection.selected base ops).op229 a b = source (encode base a) (encode base b) := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro a b
  exact R1Z.PV_CB_Op229Source.op229_source base ops a b
#print op229_source
#print axioms op229_source
end R1Z.PV_Join_Wire_Op229
