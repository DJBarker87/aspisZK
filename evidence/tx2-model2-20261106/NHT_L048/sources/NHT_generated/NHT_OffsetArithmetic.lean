import CurrentCallerUsizeArithmeticV1
set_option autoImplicit false
namespace NHT_OffsetArithmetic
open Aeneas Aeneas.Std Result
theorem sub_eq_ok (a b out : Usize) (hv : a.val-b.val=out.val)
 (hb : b.val≤a.val) : UScalar.sub a b=ok out := by
 have hs : (a-b : Result Usize) ⦃ x => x.val=a.val-b.val ⦄ := by
   apply UScalar.sub_spec
   exact hb
 obtain ⟨x,hx,hv1⟩ := WP.spec_imp_exists hs
 change (a-b : Result Usize)=ok out
 rw [hx]
 congr 1
 apply UScalar.eq_of_val_eq
 exact hv1.trans hv
#print axioms sub_eq_ok
end NHT_OffsetArithmetic
