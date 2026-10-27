import R1Z.PV_Join_Wire_Op80
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry80
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op80Transport PV_CB_Op80Exact
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    ∀ {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E), E → E → (Array E 4#usize) → Result (Array E 4#usize) :=
  fun {E} inst x y h => PV_CB_ShippedOp80.aspis_core.r0.fold.phi_inverse (encode inst) x y h
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op80 _ (PV_Join_Wire_Selection.selected base ops) = @source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext E inst x y h
  exact R1Z.PV_Join_Wire_Op80.op80_source base ops inst x y h
#print axioms equation
end R1Z.PV_Join_Wire_Entry80
