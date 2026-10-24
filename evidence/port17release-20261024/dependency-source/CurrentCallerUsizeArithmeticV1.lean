import CurrentCompactCallerModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.UsizeArithmetic

/-- Public version of the retained private helper used by SelectedClaimProofs
and SelectorValueLaneMap; reuse the library's symbolic checked-add theorem. -/
theorem add_eq_ok (a b out : Usize) (hv : a.val+b.val=out.val)
    (hb : a.val+b.val≤Usize.max) : UScalar.add a b=ok out := by
  have hs : (a+b : Result Usize) ⦃ x => x.val=a.val+b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hb
  obtain ⟨x,hx,hv1⟩ := WP.spec_imp_exists hs
  change (a+b : Result Usize)=ok out
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv1.trans hv

theorem mul_eq_ok (a b out : Usize) (hv : a.val*b.val=out.val)
    (hb : a.val*b.val≤Usize.max) : UScalar.mul a b=ok out := by
  have hs : (a*b : Result Usize) ⦃ x => x.val=a.val*b.val ⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using hb
  obtain ⟨x,hx,hv1⟩ := WP.spec_imp_exists hs
  change (a*b : Result Usize)=ok out
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  exact hv1.trans hv

#print axioms add_eq_ok
#print axioms mul_eq_ok
end AspisR1CurrentCaller.UsizeArithmetic
