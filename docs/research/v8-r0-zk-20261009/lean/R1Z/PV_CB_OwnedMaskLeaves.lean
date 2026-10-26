import R1Z.PV_CB_OwnedMask
import R1Z.PV_CB_MaskLeaves
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_OwnedMaskLeaves
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
theorem mul_i (x : C) : PV_CB_OwnedMask.owned.mul_i x =
    PV_CB_MaskSource.state_only_hiding.cm31_mul_i x := rfl
theorem mul_r (x : C) : PV_CB_OwnedMask.owned.mul_r x =
    PV_CB_MaskSource.state_only_hiding.cm31_mul_r x := rfl
theorem tower (x : Q) (i : Usize) : PV_CB_OwnedMask.owned.tower x i =
    PV_CB_MaskSource.state_only_hiding.mul_tower_basis x i := rfl
theorem tower_total (x : Q) (i : Usize) (inside : i.val<4) :
    Total (PV_CB_OwnedMask.owned.tower x i) := by
  rw [tower]
  exact PV_CB_MaskLeaves.tower x i inside
#print axioms mul_i
#print axioms mul_r
#print axioms tower
#print axioms tower_total
end R1Z.PV_CB_OwnedMaskLeaves
