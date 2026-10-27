import R1Z.PV_CB_CanonicalArrays
import R1Z.PV_CB_CanonicalQuartic
import R1Z.PV_CB_CanonicalConstants
import R1Z.PV_CB_MaskLinearsFinite
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalLinearsLoop
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange
abbrev Q := PV_CB_CanonicalTower.Q
abbrev Points := PV_CB_MaskLinearsFinite.Points
abbrev Valid := PV_CB_CanonicalTower.Valid

theorem finite (point : Points) (fuel : Nat) (e : Usize) (suffix weighted : Q)
    (rank : e.val=fuel) (bound : e.val≤10)
    (vp : PV_CB_CanonicalArrays.Valid Valid point) (vs : Valid suffix) (vw : Valid weighted) :
    ∃ outS outW, PV_CB_MaskLinearsFinite.finite point fuel e suffix weighted = ok (outS,outW) ∧
      Valid outS ∧ Valid outW := by
  induction fuel generalizing e suffix weighted with
  | zero => exact ⟨suffix,weighted,rfl,vs,vw⟩
  | succ fuel ih =>
    have inside : (pred e).val < (10#usize).val := by rw [pred_val]; change e.val-1<10; omega
    obtain ⟨q,hq,vq⟩ := PV_CB_CanonicalArrays.read Valid point vp (pred e) inside
    obtain ⟨nextS,hnextS,vnextS⟩ := PV_CB_CanonicalQuartic.add suffix q vs vq
    have weighted_step : ∃ nextW,
        (if pred e != 0#usize then PV_CB_MaskLinearsFinite.S.add weighted nextS else ok weighted) = ok nextW ∧ Valid nextW := by
      split
      · exact PV_CB_CanonicalQuartic.add weighted nextS vw vnextS
      · exact ⟨weighted,rfl,vw⟩
    obtain ⟨nextW,hnextW,vnextW⟩ := weighted_step
    obtain ⟨outS,outW,hout,voutS,voutW⟩ :=
      ih (pred e) nextS nextW (by rw [pred_val];omega) (by rw [pred_val];omega) vnextS vnextW
    refine ⟨outS,outW,?_,voutS,voutW⟩
    simp only [PV_CB_MaskLinearsFinite.finite,PV_CB_MaskLinearsFinite.S.add,
      PV_CB_CurrentQuartic.S.add] at hnextS hnextW ⊢
    simp only [hq,hnextS,hnextW,hout,bind_tc_ok]

theorem source (point : Points) (vp : PV_CB_CanonicalArrays.Valid Valid point) :
    ∃ outS outW, PV_CB_MaskLinearsFinite.S.loop (before 10#usize) point
      ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
      ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO = ok (outS,outW) ∧
      Valid outS ∧ Valid outW := by
  obtain ⟨outS,outW,hout,voutS,voutW⟩ := finite point 10 10#usize _ _ rfl (by decide)
    vp PV_CB_CanonicalConstants.zero PV_CB_CanonicalConstants.zero
  exact ⟨outS,outW,(PV_CB_MaskLinearsFinite.source point 10 10#usize _ _ rfl).trans hout,voutS,voutW⟩
#print axioms finite
#print axioms source
end R1Z.PV_CB_CanonicalLinearsLoop
