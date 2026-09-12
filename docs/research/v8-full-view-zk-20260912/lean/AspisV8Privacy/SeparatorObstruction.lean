import AspisV8Privacy.HybridBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
An exact obstruction boundary for a statement-only simulator.

This file deliberately does not assert that the retained q22 functional
separates two valid V8 witnesses.  It states the theorem that a source-level
same-public witness pair must instantiate: if one efficient Boolean observer
separates the two real proof laws by more than twice the claimed simulator
error, no single simulator depending only on the public statement can be
within that error of both real laws.
-/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section

variable {C D V X W A : Type*}
variable [Fintype C] [Fintype D] [Nonempty C] [Nonempty D]

/-- The elementary inclusion ratio for two fixed elements in an ordered
sample of `queryCount` distinct elements from `domainSize`. A source adapter
must still prove that the q22 sampler has this law. -/
def fixedPairInclusionRatio (domainSize queryCount : Nat) : ℚ :=
  (queryCount * (queryCount - 1) : ℚ) /
    (domainSize * (domainSize - 1) : ℚ)

theorem v8Q22FixedPairInclusionRatio :
    fixedPairInclusionRatio 262144 22 = 11 / 1636171776 := by
  norm_num [fixedPairInclusionRatio]

theorem v8Q22FixedPairInclusionRatio_gt_two_pow_neg28 :
    1 / (2 ^ 28 : ℚ) < fixedPairInclusionRatio 262144 22 := by
  norm_num [fixedPairInclusionRatio]

/-- Two real witness laws that share one simulator law are at distance at
most twice the simulator error for every permitted event. -/
theorem pairwise_event_advantage_le_two_mul
    (valid : X → W → Prop)
    (real : A → X → W → C → V)
    (sim : A → X → D → V)
    (allowed : A → Prop)
    (tests : (V → Bool) → Prop)
    (epsilon : ℚ)
    (hsim : ComputationalFullViewSimulationGoal valid real sim allowed tests epsilon)
    (a : A) (ha : allowed a) (x : X) (w₀ w₁ : W)
    (hw₀ : valid x w₀) (hw₁ : valid x w₁)
    (event : V → Bool) (hevent : tests event) :
    EventAdvantage (real a x w₀) (real a x w₁) event ≤ 2 * epsilon := by
  have h₀ := hsim a ha x w₀ hw₀ event hevent
  have h₁ := hsim a ha x w₁ hw₁ event hevent
  unfold EventAdvantage at h₀ h₁ ⊢
  have triangle :
      |uniformProbability (event ∘ real a x w₀) true -
          uniformProbability (event ∘ real a x w₁) true| ≤
        |uniformProbability (event ∘ real a x w₀) true -
          uniformProbability (event ∘ sim a x) true| +
        |uniformProbability (event ∘ sim a x) true -
          uniformProbability (event ∘ real a x w₁) true| := by
    rw [show uniformProbability (event ∘ real a x w₀) true -
        uniformProbability (event ∘ real a x w₁) true =
      (uniformProbability (event ∘ real a x w₀) true -
        uniformProbability (event ∘ sim a x) true) +
      (uniformProbability (event ∘ sim a x) true -
        uniformProbability (event ∘ real a x w₁) true) by ring]
    exact abs_add_le _ _
  have h₁' :
      |uniformProbability (event ∘ sim a x) true -
          uniformProbability (event ∘ real a x w₁) true| ≤ epsilon := by
    simpa [abs_sub_comm] using h₁
  calc
    |uniformProbability (event ∘ real a x w₀) true -
        uniformProbability (event ∘ real a x w₁) true|
        ≤ |uniformProbability (event ∘ real a x w₀) true -
              uniformProbability (event ∘ sim a x) true| +
            |uniformProbability (event ∘ sim a x) true -
              uniformProbability (event ∘ real a x w₁) true| := triangle
    _ ≤ epsilon + epsilon := add_le_add h₀ h₁'
    _ = 2 * epsilon := by ring

/-- Contrapositive form used by the q22 separator investigation.  The event
must belong to the declared efficient-test class; the theorem does not promote
an unbounded or witness-dependent test. -/
theorem no_statement_only_simulator_of_pairwise_separator
    (valid : X → W → Prop)
    (real : A → X → W → C → V)
    (sim : A → X → D → V)
    (allowed : A → Prop)
    (tests : (V → Bool) → Prop)
    (epsilon : ℚ)
    (a : A) (ha : allowed a) (x : X) (w₀ w₁ : W)
    (hw₀ : valid x w₀) (hw₁ : valid x w₁)
    (event : V → Bool) (hevent : tests event)
    (hsep : 2 * epsilon < EventAdvantage (real a x w₀) (real a x w₁) event) :
    ¬ ComputationalFullViewSimulationGoal valid real sim allowed tests epsilon := by
  intro hsim
  have hle := pairwise_event_advantage_le_two_mul valid real sim allowed tests epsilon
    hsim a ha x w₀ w₁ hw₀ hw₁ event hevent
  exact (not_lt_of_ge hle) hsep

/-- A deterministic decoded separator gives pairwise event advantage exactly
one.  For q22, `leak` is intended to be the public linear functional applied
to the authenticated opened C1 values; source instantiation must still prove
that the complete real view contains those values and that the two constants
come from valid witnesses for the same statement. -/
theorem deterministic_separator_advantage_one
    {Z : Type*} [DecidableEq Z]
    (real₀ real₁ : C → V) (leak : V → Z) (z₀ z₁ : Z)
    (h₀ : ∀ coins, leak (real₀ coins) = z₀)
    (h₁ : ∀ coins, leak (real₁ coins) = z₁)
    (hne : z₀ ≠ z₁) :
    EventAdvantage real₀ real₁ (fun view => decide (leak view = z₀)) = 1 := by
  classical
  have event₀ : (fun view => decide (leak view = z₀)) ∘ real₀ = fun _ => true := by
    funext coins
    simp [h₀ coins]
  have event₁ : (fun view => decide (leak view = z₀)) ∘ real₁ = fun _ => false := by
    funext coins
    have hne' : z₁ ≠ z₀ := fun h => hne h.symm
    simp [h₁ coins, hne']
  rw [EventAdvantage, event₀, event₁]
  simp [uniformProbability, fiberCount]

#print axioms pairwise_event_advantage_le_two_mul
#print axioms no_statement_only_simulator_of_pairwise_separator
#print axioms deterministic_separator_advantage_one
#print axioms v8Q22FixedPairInclusionRatio
#print axioms v8Q22FixedPairInclusionRatio_gt_two_pow_neg28

end
end AspisV8Privacy
