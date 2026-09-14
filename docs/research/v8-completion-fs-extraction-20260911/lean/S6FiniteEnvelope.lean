import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! FIRST-ATTEMPT draft. Counting/averaging consumers, not a supplied source
inclusion disguised as a completed FS theorem. The actual killed-sampler
coupling and exact ideal decoder count must produce the inputs to these leaves.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AspisS6.FiniteEnvelope
universe u v
variable {U : Type u} {V : Type v}

theorem survivor_count_le [DecidableEq U]
    (domain : Finset U) (survive event : U → Prop)
    [DecidablePred survive] [DecidablePred event] :
    (domain.filter (fun u => survive u ∧ event u)).card ≤
      (domain.filter event).card := by
  apply Finset.card_le_card
  intro u hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
    (Finset.mem_filter.mp hu).2.2⟩

theorem pointwise_inclusion_count [DecidableEq U]
    (domain : Finset U) (actual ideal : U → Prop)
    [DecidablePred actual] [DecidablePred ideal]
    (included : ∀ u ∈ domain, actual u → ideal u) :
    (domain.filter actual).card ≤ (domain.filter ideal).card := by
  apply Finset.card_le_card
  intro u hu
  obtain ⟨inside, hit⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨inside, included u inside hit⟩

/-- Averaging over a random prefix adds no division by acceptance probability.
The prefix distribution may encode arbitrary adversarial prehistory. -/
theorem prefix_average_bound [Fintype U]
    (mass actual bound : U → ℚ)
    (nonnegative : ∀ u, 0 ≤ mass u)
    (each : ∀ u, actual u ≤ bound u) :
    (∑ u, mass u * actual u) ≤ ∑ u, mass u * bound u := by
  apply Finset.sum_le_sum
  intro u _
  exact mul_le_mul_of_nonneg_left (each u) (nonnegative u)

theorem uniform_prefix_cap [Fintype U]
    (mass actual : U → ℚ) (cap : ℚ)
    (nonnegative : ∀ u, 0 ≤ mass u)
    (normalised : ∑ u, mass u = 1)
    (each : ∀ u, actual u ≤ cap) :
    (∑ u, mass u * actual u) ≤ cap := by
  have bound := prefix_average_bound mass actual (fun _ => cap) nonnegative each
  simpa only [← Finset.sum_mul, normalised, one_mul] using bound

#print axioms survivor_count_le
#print axioms pointwise_inclusion_count
#print axioms prefix_average_bound
#print axioms uniform_prefix_cap
end AspisS6.FiniteEnvelope
