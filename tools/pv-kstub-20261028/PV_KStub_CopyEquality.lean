import PV_KStub_CopyMeaning
namespace PV_KStub_CopyEquality
/-- Copy-value equality needs source agreement inside and destination agreement outside. -/
theorem transport {α : Type} (s₁ s₂ d₁ d₂ : Nat → α) (start count : Nat)
    (source : ∀ k, start ≤ k → k < start+count → s₁ k = s₂ k)
    (frame : ∀ k, ¬ (start ≤ k ∧ k < start+count) → d₁ k = d₂ k) :
    KMX_CopyMeaning.loop s₁ d₁ start count = KMX_CopyMeaning.loop s₂ d₂ start count := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases h : start ≤ k ∧ k < start+count
  · simp only [if_pos h]; exact source k h.1 h.2
  · simp only [if_neg h]; exact frame k h
#print axioms transport
end PV_KStub_CopyEquality
