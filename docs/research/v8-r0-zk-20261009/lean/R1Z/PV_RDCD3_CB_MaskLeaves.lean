import R1Z.PV_RDCD3_CB_MaskSource
import R1Z.PV_RDCD3_CB_PreparedTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_MaskLeaves
open Aeneas Aeneas.Std Result PV_RDCD3_Total
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
namespace S
abbrev power := PV_RDCD3_CB_MaskSource.state_only_hiding.mask_power_26
abbrev r := PV_RDCD3_CB_MaskSource.state_only_hiding.cm31_mul_r
abbrev i := PV_RDCD3_CB_MaskSource.state_only_hiding.cm31_mul_i
abbrev tower := PV_RDCD3_CB_MaskSource.state_only_hiding.mul_tower_basis
end S
theorem power (x : Q) : Total (S.power x) := by
  unfold S.power PV_RDCD3_CB_MaskSource.state_only_hiding.mask_power_26
  apply bind_total (PV_RDCD3_FieldTotal.q_square _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.q_square _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.q_square _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.q_square _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.q_mul _ _);intro _
  exact PV_RDCD3_FieldTotal.q_mul _ _
theorem r (x : C) : Total (S.r x) := by
  unfold S.r PV_RDCD3_CB_MaskSource.state_only_hiding.cm31_mul_r
  apply bind_total (PV_RDCD3_FieldTotal.m_double _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_sub _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_double _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_add _ _);intro _
  exact ok_total _
theorem i (x : C) : Total (S.i x) := by
  unfold S.i PV_RDCD3_CB_MaskSource.state_only_hiding.cm31_mul_i
  apply bind_total (PV_RDCD3_FieldTotal.m_neg x.b)
  intro _
  exact ok_total _
theorem tower (x : Q) (coordinate : Usize) (bound : coordinate.val < 4) :
    Total (S.tower x coordinate) := by
  have cases : coordinate.val=0 ∨ coordinate.val=1 ∨ coordinate.val=2 ∨ coordinate.val=3 := by omega
  rcases cases with h | h | h | h
  · simp only [S.tower,PV_RDCD3_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    exact ok_total _
  · simp only [S.tower,PV_RDCD3_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    apply bind_total (i _);intro _
    apply bind_total (i _);intro _
    exact ok_total _
  · simp only [S.tower,PV_RDCD3_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    apply bind_total (r _);intro _
    exact ok_total _
  · simp only [S.tower,PV_RDCD3_CB_MaskSource.state_only_hiding.mul_tower_basis,h]
    apply bind_total (r _);intro _
    apply bind_total (i _);intro _
    apply bind_total (i _);intro _
    exact ok_total _

#print axioms power
#print axioms r
#print axioms i
#print axioms tower
end R1Z.PV_RDCD3_CB_MaskLeaves
