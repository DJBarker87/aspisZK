import ChordRationalDivisibility
import ChordRationalOOD
import Mathlib.Data.Fintype.EquivFin

/-! A fixed polynomial raw message with a wrong gamma-batched OOD answer
admits at most three exact denominator-cleared alpha continuations. The final
polynomial is allowed to be an arbitrary function of alpha. No final-degree,
image, provider, recovery or verifier-acceptance premise is substituted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 100000
namespace AspisV8.ChordRationalBadOOD
noncomputable section
open Polynomial
open AspisV8.ChordRationalDegree AspisV8.ChordRationalDivisibility
open AspisV8.ChordRationalOOD AspisV8.ComponentOODBinding AspisV8.OODInterpolant
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

theorem four_exact_batched_correct (d : Data (K := K)) (checked : d.Checked)
    (U : Fin 1024 → K)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (normNonzero : clearedNorm d.a d.b d.c≠0)
    (nodes : Fin 4 → K) (distinct : Function.Injective nodes)
    (finals : Fin 4 → K[X])
    (exactAt : ∀ i : Fin 4, clearedDiscrepancy d.a d.b d.c (nodes i)
      (radialLanes (U-d.interpolant)) (finals i)=0) :
    circleFunctional d.x0 d.y0 U=d.batch 0 ∧
      circleFunctional d.x1 d.y1 U=d.batch 1 := by
  obtain ⟨q,hq⟩ := four_exact_folds_construct_polynomial_quotient d.a d.b d.c
    (radialLanes (U-d.interpolant)) nodes distinct finals normNonzero exactAt
  exact reconstructed_batched_ood d checked U q circles
    (by simpa only [radialS,radialT] using hq)

def exactChallenges (d : Data (K := K)) (U : Fin 1024 → K)
    (final : K → K[X]) (domain : Finset K) : Finset K :=
  domain.filter fun alpha => clearedDiscrepancy d.a d.b d.c alpha
    (radialLanes (U-d.interpolant)) (final alpha)=0

/-- A cardinality statement for an arbitrary finite challenge set. Uniform
sampling and transcript fixing laws are separate probability-game obligations.
The raw U and all of d are fixed across alpha; final may depend on alpha. -/
theorem wrong_batched_ood_exact_challenges_le_three
    (d : Data (K := K)) (checked : d.Checked) (U : Fin 1024 → K)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (normNonzero : clearedNorm d.a d.b d.c≠0)
    (wrong : circleFunctional d.x0 d.y0 U≠d.batch 0 ∨
      circleFunctional d.x1 d.y1 U≠d.batch 1)
    (final : K → K[X]) (domain : Finset K) :
    (exactChallenges d U final domain).card≤3 := by
  by_contra tooMany
  have many : 4≤(exactChallenges d U final domain).card := by omega
  obtain ⟨chosen,subset,four⟩ := Finset.exists_subset_card_eq many
  let enumeration : chosen ≃ Fin 4 := Finset.equivFinOfCardEq four
  let nodes : Fin 4 → K := fun i => (enumeration.symm i).val
  have distinct : Function.Injective nodes := by
    intro i j hij
    apply enumeration.symm.injective
    exact Subtype.ext hij
  have exactAt (i : Fin 4) : clearedDiscrepancy d.a d.b d.c (nodes i)
      (radialLanes (U-d.interpolant)) (final (nodes i))=0 := by
    have member := subset (enumeration.symm i).property
    exact (Finset.mem_filter.mp member).2
  have correct := four_exact_batched_correct d checked U circles normNonzero nodes
    distinct (fun i => final (nodes i)) exactAt
  rcases wrong with wrong0|wrong1
  · exact wrong0 correct.1
  · exact wrong1 correct.2

#print axioms four_exact_batched_correct
#print axioms wrong_batched_ood_exact_challenges_le_three
end
end AspisV8.ChordRationalBadOOD
