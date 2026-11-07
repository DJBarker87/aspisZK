import NNH_DistinctKeys
set_option autoImplicit false
noncomputable section
namespace NNH_DistinctModelInner
open Aeneas Aeneas.Std NGL_DistinctInduction

def Separated {N : Usize} (a : Array Account N) : Prop :=
 ∀ i j : Usize, i.val < j.val → j.val < a.val.length → keyAt a i≠keyAt a j

theorem source {N : Usize} (a : Array Account N) (small : N.val ≤ 7)
 (distinct : Separated a) (index : Usize) (inside : index.val < a.val.length)
 (fuel : Nat) (previous : Usize) (left : previous.val+fuel=index.val) :
 inner a index fuel previous=.ok none := by
 induction fuel generalizing previous with
 | zero => rfl
 | succ fuel ih =>
   have before : previous.val < index.val := by omega
   have different := distinct previous index before inside
   have inc := NFQ_ZeroPrimitives.wrap_add previous 1#usize
    (by change previous.val+1 ≤ 4096; have size:=a.property; omega)
   simp only [NGL_DistinctInduction.inner,if_neg different]
   exact ih _ (by rw [inc]; omega)
#print axioms source
end NNH_DistinctModelInner
