import FJa_FoldShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SplitMass
open FIv_NativeValue (K)
/-- Pair adjacent children symbolically; no finite concrete selector table. -/
theorem pairs (g : Nat → K) (n : Nat) :
    (∑ j∈Finset.range (2*n),g j)=∑ i∈Finset.range n,(g (2*i)+g (2*i+1)) := by
  induction n with
  | zero => simp only [Nat.mul_zero,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    rw [show 2*(n+1)=(2*n+1)+1 by omega,Finset.sum_range_succ,
      Finset.sum_range_succ,ih,Finset.sum_range_succ]
    exact add_assoc _ _ _
/-- A complete descending split doubles width and preserves total mass. -/
theorem value (c : K) (f : Nat → K) (n : Nat) :
    (∑ j∈Finset.range (2*n),FJa_SplitModel.fold c n f j)=∑ i∈Finset.range n,f i := by
  rw [pairs]
  apply Finset.sum_congr rfl
  intro i hi
  have h := FJa_FoldShape.children c f n i (Finset.mem_range.mp hi)
  rw [h.1,h.2]
  exact sub_add_cancel _ _
#print axioms pairs
#print axioms value
end AspisR1.FJa_SplitMass
end
