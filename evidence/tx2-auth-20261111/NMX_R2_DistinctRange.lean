import NMX_DistinctPredicate
set_option autoImplicit false
noncomputable section
namespace NMX_R2_DistinctRange
open Aeneas Aeneas.Std AdapterRw NGL_DistinctInduction NMX_DistinctPredicate
/-- The native loop's key projection at an ordinary index, still symbolic. -/
def nthKey {N : Usize} (a : Array Account N) (i : Nat) :=
 (a.val[i]?).map (fun x => x.key)

theorem inner {N : Usize} (a : Array Account N) (index : Usize)
 (n : Nat) (previous : Usize) (small : previous.val+n≤7) :
 before a index n previous ↔
 ∀ k, previous.val≤k → k<previous.val+n → nthKey a k ≠ nthKey a index.val := by
 induction n generalizing previous with
 | zero =>
   simp only [before]
   constructor
   · intro _ k lower upper
     omega
   · intro _
     trivial
 | succ n ih =>
   have inc : (Usize.wrapping_add previous 1#usize).val = previous.val+1 :=
    NFQ_ZeroPrimitives.wrap_add previous 1#usize (by change previous.val+1≤4096; omega)
   rw [before,ih _ (by rw [inc]; omega)]
   change (nthKey a previous.val ≠ nthKey a index.val ∧ _) ↔ _
   constructor
   · intro h k lower upper
     by_cases atStart : k=previous.val
     · subst k
       exact h.1
     · exact h.2 k (by rw [inc]; omega) (by rw [inc]; omega)
   · intro h
     exact ⟨h previous.val (by omega) (by omega),fun k lower upper =>
       h k (by rw [inc] at lower; omega) (by rw [inc] at upper; omega)⟩
#print axioms inner
end NMX_R2_DistinctRange
end
