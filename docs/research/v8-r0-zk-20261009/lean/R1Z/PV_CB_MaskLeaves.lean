import R1Z.PV_CB_MaskSource
import R1Z.PV_CB_PreparedTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskLeaves
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
namespace S
abbrev power := PV_CB_MaskSource.state_only_hiding.mask_power_26
abbrev r := PV_CB_MaskSource.state_only_hiding.cm31_mul_r
abbrev i := PV_CB_MaskSource.state_only_hiding.cm31_mul_i
abbrev tower := PV_CB_MaskSource.state_only_hiding.mul_tower_basis
end S
theorem power (x : Q) : Total (S.power x) := by
  unfold S.power PV_CB_MaskSource.state_only_hiding.mask_power_26
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_square _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_mul _ _);intro _
  exact PV_CB_CurrentTotal.q_mul _ _
theorem r (x : C) : Total (S.r x) := by
  unfold S.r PV_CB_MaskSource.state_only_hiding.cm31_mul_r
  apply bind_total (PV_CB_CurrentTotal.m_double _);intro _
  apply bind_total (PV_CB_CurrentTotal.m_sub _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.m_double _);intro _
  apply bind_total (PV_CB_CurrentTotal.m_add _ _);intro _
  exact ok_total _
theorem i (x : C) : Total (S.i x) := by
  unfold S.i PV_CB_MaskSource.state_only_hiding.cm31_mul_i
  apply bind_total ((congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentNeg.native x.b)).mpr (m_neg _))
  intro _
  exact ok_total _
theorem tower (x : Q) (coordinate : Usize) (bound : coordinate.val < 4) :
    Total (S.tower x coordinate) := by
  have cases : coordinate.val=0 ∨ coordinate.val=1 ∨ coordinate.val=2 ∨ coordinate.val=3 := by omega
  rcases cases with h | h | h | h
  · simp only [S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    exact ok_total _
  · simp only [S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    apply bind_total (i _);intro _
    apply bind_total (i _);intro _
    exact ok_total _
  · simp only [S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    apply bind_total (r _);intro _
    exact ok_total _
  · simp only [S.tower,PV_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    apply bind_total (r _);intro _
    apply bind_total (i _);intro _
    apply bind_total (i _);intro _
    exact ok_total _

#print axioms power
#print axioms r
#print axioms i
#print axioms tower
end R1Z.PV_CB_MaskLeaves
