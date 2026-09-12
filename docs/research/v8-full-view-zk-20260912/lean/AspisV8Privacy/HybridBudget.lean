import AspisV8Privacy.PrivacyGames
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. Deterministic triangle accounting only.
No numerical privacy budget for V8 is claimed or populated by this module.
-/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section
variable {C D E V : Type*}
variable [Fintype C] [Fintype D] [Fintype E]
variable [Nonempty C] [Nonempty D] [Nonempty E]

theorem event_distance_trans (f : C → V) (g : D → V) (h : E → V)
    (eps₁ eps₂ : ℚ) (h₁ : EventDistanceBound f g eps₁) (h₂ : EventDistanceBound g h eps₂) :
    EventDistanceBound f h (eps₁ + eps₂) := by
  intro event
  have h₁' := h₁ event
  have h₂' := h₂ event
  unfold EventAdvantage at h₁' h₂' ⊢
  have triangle :
      |uniformProbability (event ∘ f) true - uniformProbability (event ∘ h) true| ≤
        |uniformProbability (event ∘ f) true - uniformProbability (event ∘ g) true| +
        |uniformProbability (event ∘ g) true - uniformProbability (event ∘ h) true| := by
    rw [show uniformProbability (event ∘ f) true - uniformProbability (event ∘ h) true =
      (uniformProbability (event ∘ f) true - uniformProbability (event ∘ g) true) +
      (uniformProbability (event ∘ g) true - uniformProbability (event ∘ h) true) by ring]
    exact abs_add_le _ _
  exact triangle.trans (add_le_add h₁' h₂')

/-- Exact equality removes a hop without treating it as an independent event. -/
theorem pointwise_same_game (f g : C → V) (same : ∀ coins, f coins = g coins) :
    EventDistanceBound f g 0 := by
  have eq : f = g := funext same
  subst g
  intro event
  simp [EventAdvantage]

#print axioms event_distance_trans
#print axioms pointwise_same_game
end
end AspisV8Privacy
