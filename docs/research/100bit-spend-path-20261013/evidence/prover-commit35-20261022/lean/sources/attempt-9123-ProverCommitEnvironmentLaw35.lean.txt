import R1Z.ProverCommitEnvironment35
/-! The only named environment trust item is E1. This module derives its
conditional zero-candidate bound; it asserts no bound on OS/fs failures.
All finite sums are symbolic, never enumerations of concrete byte spaces. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEnvironmentLaw35
open R0Z R0Z.FsAbort ProverCommitEnvironment35 ProverCommitEntropy18
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def conditionalMass {Context : Type} (okLaw : Context → Candidate → ℚ)
    (context : Context) (event : Candidate → Prop) : ℚ :=
  ∑ raw, if event raw then okLaw context raw else 0

/-- Pointwise E1 applies for every prior context, including the adversarial
schedule, ledger, witness and every previous RNG return. -/
theorem E1_event {Context : Type} (okLaw : Context → Candidate → ℚ)
    (environment_rng_E1 : E1 okLaw) (context : Context) (event : Candidate → Prop) :
    conditionalMass okLaw context event = eventMass event := by
  unfold conditionalMass eventMass mean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro raw _
  by_cases h : event raw
  · simp only [if_pos h,environment_rng_E1 context raw]
  · simp only [if_neg h,zero_div]

/-- The inherited 3/2^256 term remains valid conditionally on every history.
This is first-candidate zero rejection, which contains zero exhaustion.
No assertion about the likelihood of obtaining Ok is involved. -/
theorem E1_zero_candidate {Context : Type} (okLaw : Context → Candidate → ℚ)
    (environment_rng_E1 : E1 okLaw) (context : Context) :
    conditionalMass okLaw context (fun raw => decode raw = none) ≤
      ProverCommitEntropy34.zeroBudget := by
  rw [E1_event okLaw environment_rng_E1 context]
  exact ProverCommitEntropy34.candidate_bad_mass

#print axioms E1_event
#print axioms E1_zero_candidate
end R1Z.ProverCommitEnvironmentLaw35
