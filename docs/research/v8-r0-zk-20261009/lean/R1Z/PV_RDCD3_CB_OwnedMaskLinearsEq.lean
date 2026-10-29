import R1Z.PV_RDCD3_CB_OwnedMaskLinears
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_OwnedMaskLinearsEq
open Aeneas Aeneas.Std Result PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
set_option backward.isDefEq.respectTransparency false in
theorem source (point : Array Q 10#usize) : PV_RDCD3_CB_OwnedMask.owned.linears point =
    PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears point := by
  unfold PV_RDCD3_CB_OwnedMask.owned.linears PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears
  simp only [core.iter.traits.iterator.Iterator.rev.default,core.iter.traits.iterator.Iterator.rev.trait_default,bind_tc_ok,
    PV_RDCD3_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS]
  rw [PV_RDCD3_CB_OwnedMaskLinears.source point 10 10#usize _ _ rfl]
  have h := PV_RDCD3_CB_MaskLinearsFinite.source point 10 10#usize
    PV_RDCD3_FieldSource.aspis_core.field.QM31.ZERO
    PV_RDCD3_FieldSource.aspis_core.field.QM31.ZERO rfl
  unfold PV_RDCD3_CB_MaskLinearsFinite.S.loop before at h
  rw [h]
#print axioms source
end R1Z.PV_RDCD3_CB_OwnedMaskLinearsEq
