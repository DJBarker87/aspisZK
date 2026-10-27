import R1Z.PV_CB_CanonicalPreparedMul
import R1Z.PV_CB_CanonicalQuartic
import R1Z.PV_CB_MaskHorner
import R1Z.PV_CB_OwnedMaskHornerEq
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalHorner
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange
abbrev Q := PV_CB_CanonicalTower.Q
abbrev Coeff := PV_CB_MaskHorner.Coeff
abbrev Prepared := PV_CB_CanonicalPreparedCtor.Prepared

theorem finite (coeff : Coeff) (prepared : Prepared) (fuel : Nat)
    (e : Usize) (shared : Q) (rank : e.val = fuel) (bound : e.val ≤ 27)
    (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff)
    (vp : PV_CB_CanonicalPreparedCtor.Valid prepared) (vs : PV_CB_CanonicalTower.Valid shared) :
    ∃ out, PV_CB_MaskHorner.finite coeff prepared fuel e shared = ok out ∧
      PV_CB_CanonicalTower.Valid out := by
  induction fuel generalizing e shared with
  | zero => exact ⟨shared,rfl,vs⟩
  | succ fuel ih =>
    have next_rank : (pred e).val = fuel := by rw [pred_val]; omega
    have inside : (pred e).val < 27 := by rw [pred_val]; omega
    obtain ⟨coefficient,hcoefficient,vcoefficient⟩ :=
      PV_CB_CanonicalArrays.read PV_CB_CanonicalTower.Valid coeff vc (pred e) inside
    obtain ⟨product,hproduct,vproduct⟩ := PV_CB_CanonicalPreparedMul.mul prepared shared vp vs
    obtain ⟨next,hnext,vnext⟩ := PV_CB_CanonicalQuartic.add product coefficient vproduct vcoefficient
    obtain ⟨out,hout,vout⟩ := ih (pred e) next next_rank (by omega) vnext
    refine ⟨out,?_,vout⟩
    simp only [PV_CB_MaskHorner.finite,PV_CB_MaskHorner.S.mul,
      PV_CB_MaskHorner.S.add,PV_CB_PreparedTotal.S.mul,PV_CB_CurrentQuartic.S.add] at hproduct hnext ⊢
    simp only [hproduct,hcoefficient,hnext,hout,bind_tc_ok]

theorem source (coeff : Coeff) (prepared : Prepared) (e : Usize) (shared : Q)
    (bound : e.val ≤ 27)
    (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff)
    (vp : PV_CB_CanonicalPreparedCtor.Valid prepared) (vs : PV_CB_CanonicalTower.Valid shared) :
    ∃ out, PV_CB_MaskHorner.S.loop (before e) coeff prepared shared = ok out ∧
      PV_CB_CanonicalTower.Valid out := by
  obtain ⟨out,hout,vout⟩ := finite coeff prepared e.val e shared rfl bound vc vp vs
  exact ⟨out,(PV_CB_MaskHorner.source coeff prepared e.val e shared rfl).trans hout,vout⟩

theorem owned (coeff : Coeff) (prepared : Prepared) (e : Usize) (shared : Q)
    (bound : e.val ≤ 27)
    (vc : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalTower.Valid coeff)
    (vp : PV_CB_CanonicalPreparedCtor.Valid prepared) (vs : PV_CB_CanonicalTower.Valid shared) :
    ∃ out, PV_CB_OwnedMask.owned.horner coeff prepared e shared = ok out ∧
      PV_CB_CanonicalTower.Valid out := by
  obtain ⟨out,hout,vout⟩ := source coeff prepared e shared bound vc vp vs
  exact ⟨out,(PV_CB_OwnedMaskHornerEq.source coeff prepared e shared).trans hout,vout⟩
#print axioms finite
#print axioms source
#print axioms owned
end R1Z.PV_CB_CanonicalHorner
