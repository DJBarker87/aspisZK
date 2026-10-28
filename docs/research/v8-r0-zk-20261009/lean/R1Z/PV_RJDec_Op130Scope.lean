import R1Z.PV_RDCD_ZeroConsumed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_Op130Scope
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- Exact scope of the restored op122/op123 installation. It does not install op130. -/
theorem unchanged (ops : ExternalFuns) {Z : Type} (d : zeroize.Zeroize Z)
    (v : zeroize.Zeroizing Z) :
    (PV_RDCD_ZeroSelected.selected ops).op130 d v=ops.op130 d v := rfl
/-- A countermodel to inferring the wrapper from byte/array fields alone,
not a counterexample to the deployed Zeroizing body. -/
theorem independent (ops : ExternalFuns) {Z : Type} (d : zeroize.Zeroize Z)
    (v : zeroize.Zeroizing Z) :
    let left := PV_RDCD_ZeroSelected.selected {ops with op130 := fun _ z => .ok z}
    let right := PV_RDCD_ZeroSelected.selected {ops with op130 := fun _ _ => .div}
    left.op122 = right.op122 ∧ left.op123 = right.op123 ∧ left.op130 d v ≠ right.op130 d v := by
  exact ⟨rfl,rfl,by intro h; cases h⟩
#print axioms unchanged
#print axioms independent
end R1Z.PV_RJDec_Op130Scope
