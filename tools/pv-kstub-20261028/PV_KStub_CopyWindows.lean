import PV_KStub_CopyMeaning
namespace PV_KStub_CopyWindows
/-- Adjacent indexed windows compose to the complete copy; untouched cells stay framed. -/
theorem adjacent {α : Type} (src dst : Nat → α) (start a b : Nat) :
    KMX_CopyMeaning.loop src dst start (a+b) =
      KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst start a) (start+a) b := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases h₁ : start ≤ k ∧ k < start + a
  · have h₂ : ¬ (start+a ≤ k ∧ k < start+a+b) := by omega
    have h₃ : start ≤ k ∧ k < start+(a+b) := by omega
    simp only [if_pos h₁, if_neg h₂, if_pos h₃]
  · by_cases h₂ : start+a ≤ k ∧ k < start+a+b
    · have h₃ : start ≤ k ∧ k < start+(a+b) := by omega
      simp only [if_neg h₁, if_pos h₂, if_pos h₃]
    · have h₃ : ¬ (start ≤ k ∧ k < start+(a+b)) := by omega
      simp only [if_neg h₁, if_neg h₂, if_neg h₃]
#print axioms adjacent
end PV_KStub_CopyWindows
