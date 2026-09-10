import SingularOODFamily
import SelectedLinearCover

/-! The fixed product and additive budgets on the actual selected C1/C2
parent. The pair-root event is not assigned a sampler probability. Singular
gammas include all retained higher factors, regardless of adaptive Q/finals.
Source-review draft only; check the generic family predecessor first.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.SelectedSingularOODFamily
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.SelectedFactorCoherence
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant
open AspisV8.SingularOODFamily
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
attribute [local irreducible] curvePrimeFactors

/-- Fixed from authenticated-word interfaces C1/C2 only. This is a
mathematical fixed-word interface, not a new authentication theorem. -/
def obstruction (c1 : C1Received) (c2 : C2Received) : K[X] :=
  parentObstruction (parent c1 c2)

theorem fixed_cover (c1 : C1Received) (c2 : C2Received) :
    obstruction c1 c2 ≠ 0 ∧ (obstruction c1 c2).natDegree ≤ 25345827 ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]) (Gamma : Finset K),
        (∀ r, (answers r).natDegree ≤ 28) →
        (∀ r, (obstruction c1 c2).eval (points r)=0) ∨
          (singularGammas (parent c1 c2) points answers Gamma).card ≤ 117049 := by
  have nonzero : parent c1 c2 ≠ 0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  have yDegree := SelectedLinearCover.parent_y_degree c1 c2
  have xDegree := SelectedMonicCover.parent_x_degree c1 c2
  have weight := trivariateYZWeight_curveTrivariatePolynomial_lt
    (by norm_num : 0 < 117078) (fixedInterpolant c1 c2)
  change trivariateYZWeight 28 (parent c1 c2) < 117078 at weight
  have nonzeroE := exactV7_parent_obstruction_nonzero (parent c1 c2) nonzero (by omega)
  have degreeE := parent_obstruction_degree (parent c1 c2) nonzero
  refine ⟨nonzeroE, ?_, ?_⟩
  · have size : 2*(parent c1 c2).natDegree-1 ≤ 221 := by omega
    have bound := degreeE.trans (Nat.mul_le_mul size xDegree)
    exact bound
  · intro points answers Gamma degrees
    rcases singular_count_or 28 (parent c1 c2) nonzero points answers Gamma degrees
      with pairRoots | small
    · exact Or.inl pairRoots
    · exact Or.inr (small.trans (by omega))

/-- Actual normalized OOD points and answer curves, with their existing
degree28 source bound. No checked/image/final condition is necessary to
bound this larger singular event. -/
theorem actual_prefix_count (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (Gamma : Finset K) :
    (∀ r, (obstruction c1 c2).eval (point d r)=0) ∨
      (singularGammas (parent c1 c2) (point d)
        (fun r => CurveOODGate.answerCurve (answers d r)) Gamma).card ≤ 117049 :=
  (fixed_cover c1 c2).2.2 (point d)
    (fun r => CurveOODGate.answerCurve (answers d r)) Gamma (answers_degree d)

#print axioms fixed_cover
#print axioms actual_prefix_count
end
end AspisV8.SelectedSingularOODFamily
