import R1Z.PV_Join_Wire_Selection
import R1Z.PV_CB_Op80Exact
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op80
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op80Transport PV_CB_Op80Exact
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem op80_source (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    ∀ {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Array E 4#usize),
    (PV_Join_Wire_Selection.selected base ops).op80 inst x y h =
      PV_CB_ShippedOp80.aspis_core.r0.fold.phi_inverse (encode inst) x y h := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  intro E inst x y h
  exact R1Z.PV_CB_Op80Exact.op80_source ops inst x y h
#print op80_source
#print axioms op80_source
end R1Z.PV_Join_Wire_Op80
