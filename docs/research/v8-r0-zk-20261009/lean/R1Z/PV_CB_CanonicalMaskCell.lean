import R1Z.PV_CB_CanonicalUpdate
import R1Z.PV_CB_CanonicalMaskBasis
import R1Z.PV_CB_MaskCell
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalMaskCell
open Aeneas Aeneas.Std Result
abbrev Q := PV_CB_CanonicalTower.Q
abbrev Coeff := PV_CB_MaskCell.Coeff

theorem cell {N : Usize} (data : Array Q N) (exponents : Array U8 N)
    (column : Usize) (coeff : Coeff) (inside : column.val < N.val)
    (exponent_safe : ∃ value, Array.index_usize exponents column = ok value ∧ value.val < 27)
    (vd : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid data)
    (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff) :
    ∃ out, PV_CB_MaskCell.cell data exponents column coeff = ok out ∧
      PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid out := by
  obtain ⟨q,hq,vq⟩ := PV_CB_CanonicalArrays.read PV_CB_CanonicalTower.Valid data vd column inside
  obtain ⟨value,hvalue,vvalue⟩ :=
    PV_CB_CanonicalMaskBasis.tower q (column &&& 3#usize) (PV_CB_MaskIndices.coordinate column) vq
  obtain ⟨exponent,hexponent,bound⟩ := exponent_safe
  have slot_bound : (core.convert.num.FromUsizeU8.from exponent).val < (27#usize).val := by
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    exact bound
  obtain ⟨out,hout,vout⟩ := PV_CB_CanonicalUpdate.update PV_CB_CanonicalTower.Valid coeff _ value slot_bound vc vvalue
  refine ⟨out,?_,vout⟩
  simp only [PV_CB_MaskCell.cell,hq,hvalue,hexponent,lift,bind_tc_ok,hout]
#print axioms cell
end R1Z.PV_CB_CanonicalMaskCell
