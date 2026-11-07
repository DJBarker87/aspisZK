import NNH_DistinctModelInner
set_option autoImplicit false
noncomputable section
namespace NNH_DistinctModelOuter
open Aeneas Aeneas.Std NGL_DistinctInduction

theorem source {N : Usize} (a : Array Account N) (small : N.val ≤ 7)
 (distinct : NNH_DistinctModelInner.Separated a)
 (fuel : Nat) (index : Usize) (left : index.val+fuel=N.val) :
 outer a fuel index=.ok none := by
 induction fuel generalizing index with
 | zero => rfl
 | succ fuel ih =>
   have inside : index.val < a.val.length := by rw [a.property]; omega
   have head := NNH_DistinctModelInner.source a small distinct index inside index.val 0#usize
    (by change 0+index.val=index.val; omega)
   have inc : (Usize.wrapping_add index 1#usize).val=index.val+1 := NFQ_ZeroPrimitives.wrap_add index 1#usize
    (by change index.val+1 ≤ 4096; omega)
   simp only [NGL_DistinctInduction.outer,head,bind_tc_ok]
   exact ih (Usize.wrapping_add index 1#usize) (by omega)
#print axioms source
end NNH_DistinctModelOuter
