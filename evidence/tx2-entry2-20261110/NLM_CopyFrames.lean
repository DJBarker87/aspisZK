import KMX_CopyMeaning
set_option autoImplicit false
namespace NLM_CopyFrames
/-- Compose adjacent KMX windows symbolically; untouched coordinates are
retained. Native pointer validity, allocation and non-overlap remain cuts. -/
theorem adjacent {α : Type} (src dst : Nat → α) (start n m : Nat) :
 KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst start n) (start+n) m=
 KMX_CopyMeaning.loop src dst start (n+m) := by
 funext k
 simp only [KMX_CopyMeaning.loop_spec]
 by_cases right : start+n≤k ∧ k<start+n+m
 · have all : start≤k ∧ k<start+(n+m) := by omega
   rw [if_pos right,if_pos all]
 · rw [if_neg right]
   by_cases left : start≤k ∧ k<start+n
   · have all : start≤k ∧ k<start+(n+m) := by omega
     rw [if_pos left,if_pos all]
   · have none : ¬ (start≤k ∧ k<start+(n+m)) := by omega
     rw [if_neg left,if_neg none]

theorem inside {α : Type} (src dst : Nat → α) (n k : Nat) (hk : k<n) :
 KMX_CopyMeaning.loop src dst 0 n k=src k := by
 rw [KMX_CopyMeaning.copy_prefix,if_pos hk]

theorem outside {α : Type} (src dst : Nat → α) (n k : Nat) (hk : n≤k) :
 KMX_CopyMeaning.loop src dst 0 n k=dst k :=
 KMX_CopyMeaning.copy_frame src dst 0 n k (Or.inr (by simpa using hk))
#print adjacent
#print inside
#print outside
#print axioms adjacent
#print axioms inside
#print axioms outside
end NLM_CopyFrames
