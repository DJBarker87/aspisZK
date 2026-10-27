import R1Z.PV_CB_CanonicalForward
import R1Z.PV_CB_CanonicalMaskCell
import R1Z.PV_CB_FillLoopsEq
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalFill
open Aeneas Aeneas.Std Result PV_CB_ForwardRange
abbrev Q := PV_CB_CanonicalTower.Q
abbrev Coeff := PV_CB_MaskCell.Coeff
abbrev Valid {N : Usize} (values : Array Q N) :=
  PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid values

theorem c1 (data : Array Q 16#usize) (coeff : Coeff) (vd : Valid data) (vc : Valid coeff) :
    ∃ out, PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop0
      (between 0#usize 16#usize) data coeff = ok out ∧ Valid out := by
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalForward.finite Valid
    (PV_CB_MaskCell.cell data PV_CB_MaskIndices.S.factors) 16#usize
    (fun i hi state vs => PV_CB_CanonicalMaskCell.cell data _ i state hi
      (PV_CB_MaskIndices.factors_read i hi) vd vs) 16 0#usize coeff rfl vc
  exact ⟨out,(PV_CB_MaskFillLoop.c1_finite data 16 0#usize 16#usize coeff rfl).trans hout,vout⟩

theorem mask (data : Array Q 10#usize) (coeff : Coeff) (vd : Valid data) (vc : Valid coeff) :
    ∃ out, PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop1
      (between 0#usize 10#usize) data coeff = ok out ∧ Valid out := by
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalForward.finite Valid
    (PV_CB_MaskCell.cell data PV_CB_MaskIndices.S.maskFactors) 10#usize
    (fun i hi state vs => PV_CB_CanonicalMaskCell.cell data _ i state hi
      (PV_CB_MaskIndices.mask_factors_read i hi) vd vs) 10 0#usize coeff rfl vc
  exact ⟨out,(PV_CB_MaskFillLoop.mask_finite data 10 0#usize 10#usize coeff rfl).trans hout,vout⟩

theorem owned_c1 (data : Array Q 16#usize) (coeff : Coeff) (vd : Valid data) (vc : Valid coeff) :
    ∃ out, PV_CB_OwnedMask.owned.fill_c1 data coeff 0#usize = ok out ∧ Valid out := by
  obtain ⟨out,hout,vout⟩ := c1 data coeff vd vc
  exact ⟨out,(PV_CB_FillLoopsEq.c1 data coeff).trans hout,vout⟩

theorem owned_mask (data : Array Q 10#usize) (coeff : Coeff) (vd : Valid data) (vc : Valid coeff) :
    ∃ out, PV_CB_OwnedMask.owned.fill_mask data coeff 0#usize = ok out ∧ Valid out := by
  obtain ⟨out,hout,vout⟩ := mask data coeff vd vc
  exact ⟨out,(PV_CB_FillLoopsEq.mask data coeff).trans hout,vout⟩
#print axioms c1
#print axioms mask
#print axioms owned_c1
#print axioms owned_mask
end R1Z.PV_CB_CanonicalFill
