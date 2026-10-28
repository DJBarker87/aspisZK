import R1Z.PV_RunJoin_MergeFold35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeSum35
open PV_RunJoin_MergeFold35

def total (e : Nat → F) (a k : Nat) : Nat → Nat → F
  | _,0 => 0
  | i,n+1 => (if i/a=k then e i else 0)+total e a k (i+1) n

/-- Exact semantic cell meaning of the ordered source merge. The quotient
filter selects precisely this sample's assignments and preserves all others. -/
theorem cell (n : Nat) (p e : Nat → F) (a i k : Nat) :
    fold n p e a i k = p k + total e a k i n := by
  induction n generalizing p i with
  | zero => simp only [fold,total,add_zero]
  | succ n ih =>
    rw [fold,ih,total]
    by_cases h : k=i/a
    · subst k
      simp only [Function.update_self,if_true]
      exact add_assoc _ _ _
    · simp only [Function.update_of_ne h,Ne.symm h,if_false,zero_add]

theorem sum (e : Nat → F) (a k i n : Nat) :
    total e a k i n = ∑ j ∈ Finset.range n, if (i+j)/a=k then e (i+j) else 0 := by
  induction n generalizing i with
  | zero => simp only [total,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    rw [total,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have h : i+1+j=i+(j+1) := by omega
    rw [h]

#print axioms cell
#print axioms sum
end R1Z.PV_RunJoin_MergeSum35
