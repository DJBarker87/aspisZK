import KMX_CopyMeaning
set_option autoImplicit false
namespace NHD_CopyWindows

/-- Adjacent windows compose using the retained KMX value law, for arbitrary length. -/
theorem split {α : Type} (src dst : Nat → α) (start left right : Nat) :
    KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst start left)
      (start+left) right = KMX_CopyMeaning.loop src dst start (left+right) := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases hr : start+left ≤ k ∧ k < start+left+right
  · have total : start ≤ k ∧ k < start+(left+right) := by omega
    simp only [if_pos hr,if_pos total]
  · by_cases hl : start ≤ k ∧ k < start+left
    · have total : start ≤ k ∧ k < start+(left+right) := by omega
      simp only [if_neg hr,if_pos hl,if_pos total]
    · have outside : ¬ (start ≤ k ∧ k < start+(left+right)) := by omega
      simp only [if_neg hr,if_neg hl,if_neg outside]

/-- Exact one-cell decomposition, without a concrete large recurrence evaluation. -/
theorem one_then_rest {α : Type} (src dst : Nat → α) (start rest : Nat) :
    KMX_CopyMeaning.loop src (KMX_CopyMeaning.write dst start (src start))
      (start+1) rest = KMX_CopyMeaning.loop src dst start (rest+1) := by
  rw [KMX_CopyMeaning.loop]

#print axioms split
#print axioms one_then_rest
end NHD_CopyWindows
