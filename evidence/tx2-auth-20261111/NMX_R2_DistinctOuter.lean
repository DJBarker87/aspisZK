import NMX_R2_DistinctRange
set_option autoImplicit false
noncomputable section
namespace NMX_R2_DistinctOuter
open Aeneas Aeneas.Std AdapterRw NGL_DistinctInduction NMX_DistinctPredicate
open NMX_R2_DistinctRange
/-- Symbolic outer scan covers exactly the ordered pairs before its bound. -/
theorem range {N : Usize} (a : Array Account N) (n : Nat) (index : Usize)
 (small : index.val+n≤7) :
 unique a n index ↔
 ∀ i, index.val≤i → i<index.val+n → ∀ j, j<i → nthKey a j ≠ nthKey a i := by
 induction n generalizing index with
 | zero =>
   simp only [unique]
   constructor
   · intro _ i lower upper
     omega
   · intro _
     trivial
 | succ n ih =>
   have inc : (Usize.wrapping_add index 1#usize).val=index.val+1 :=
    NFQ_ZeroPrimitives.wrap_add index 1#usize (by change index.val+1≤4096; omega)
   rw [unique,NMX_R2_DistinctRange.inner a index index.val 0#usize (by change 0+index.val≤7; omega),
    ih _ (by rw [inc]; omega)]
   constructor
   · intro h i lower upper j earlier
     by_cases first : i=index.val
     · subst i
       exact h.1 j (by change 0≤j; omega) (by change j<0+index.val; omega)
     · exact h.2 i (by rw [inc]; omega) (by rw [inc]; omega) j earlier
   · intro h
     constructor
     · intro j lower upper
       exact h index.val (by omega) (by omega) j (by change j<0+index.val at upper; omega)
     · intro i lower upper j earlier
       exact h i (by rw [inc] at lower; omega) (by rw [inc] at upper; omega) j earlier
#print axioms range
end NMX_R2_DistinctOuter
end
