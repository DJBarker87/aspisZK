import SelectedLinearCover
import SelectedQuadraticCover

/-!
Refine the same selected retained-root classification: quadratic factors
are charged to the checked fixed OOD polynomial or fixed gamma set. Every
earlier linear exception, sparse challenge and actual tuple alternative is
preserved. Degree at least three remains a named same-candidate remainder.
No accepting-proof implication or pre-lambda tuple selection is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedQuadraticReduction
namespace Generic
noncomputable section
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV8.FactorIdentityCover
variable {k : Type*} [Field k]

/-- Split only the actual degree of the same retained factor. The supplied
quadratic control is universal over every adaptive polynomial candidate. -/
theorem refine_higher (P : TrivariatePolynomial k) (E : k[X]) (B : Finset k)
    (points : Fin 2 → k) (answers : Fin 2 → k[X]) (gamma : k) (U : k[X])
    (quadratic : (∃ F ∈ curvePrimeFactors P, F.natDegree = 2 ∧
      (∀ r, FactorCoherence.pointSubstitution (points r) (answers r) F = 0) ∧
      challengeCandidateHom gamma U F = 0) →
      (∀ r, E.eval (points r) = 0) ∨ gamma ∈ B)
    (higher : ∃ F ∈ curvePrimeFactors P, Retained points answers F ∧
      challengeCandidateHom gamma U F = 0 ∧ 2 ≤ F.natDegree) :
    (∀ r, E.eval (points r) = 0) ∨ gamma ∈ B ∨
      ∃ F ∈ curvePrimeFactors P, Retained points answers F ∧
        challengeCandidateHom gamma U F = 0 ∧ 3 ≤ F.natDegree := by
  obtain ⟨F, member, retained, candidate, lower⟩ := higher
  by_cases degree : F.natDegree = 2
  · rcases quadratic ⟨F, member, degree, retained.2, candidate⟩ with hit | bad
    · exact Or.inl hit
    · exact Or.inr (Or.inl bad)
  · exact Or.inr (Or.inr ⟨F, member, retained, candidate, by omega⟩)

#print axioms refine_higher
end
end Generic

noncomputable section
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.SelectedFactorCoherence AspisV8.SelectedIdentityCover
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.FactorIdentityCover
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors
attribute [local irreducible] LinearMessageFamily.family LinearMessageFamily.sparseChallenges

/-- The remaining nonlinear factor belongs to the same fixed family and
annihilates the same original-Q GRS polynomial; nothing is reselected. -/
def HigherCubicRoot (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (gamma : K) (Q : Fin 1024 → K) : Prop :=
  ∃ F ∈ curvePrimeFactors (parent c1 c2),
    Retained (point d) (fun r => CurveOODGate.answerCurve (answers d r)) F ∧
    challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) F = 0 ∧
    3 ≤ F.natDegree

/-- The older linear OOD/sparse alternatives are kept individually, rather
than hidden in a claim that quadratic removal completes extraction. -/
def Outcome (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K)
    (linearE quadraticE : K[X]) (quadraticBad : Finset K)
    (d : Data (K := K)) (gamma : K) (Q : Fin 1024 → K) : Prop :=
  (∀ r, linearE.eval (point d r) = 0) ∨
    gamma ∈ LinearMessageFamily.sparseChallenges (parent c1 c2) Gamma ∨
    (∀ r, quadraticE.eval (point d r) = 0) ∨
    gamma ∈ quadraticBad ∨
    HigherCubicRoot c1 c2 d gamma Q ∨
    ∃ messages ∈ LinearMessageFamily.family (parent c1 c2),
      (atGamma d gamma).original Q =
        ∑ j : Fin 29, gamma^j.val • messages j

/-- Both OOD polynomials and the quadratic exceptional set are selected
before d, gamma and Q. The inherited tuple family is unchanged. The linear
sparse set also depends on the supplied fixed challenge universe Gamma.
This consumes Root, not verifier acceptance; the earlier identity-cover
gamma exception is not discarded by asserting that Root always holds. -/
theorem exists_selected_reduction (c1 : C1Received) (c2 : C2Received)
    (Gamma : Finset K) :
    ∃ linearE quadraticE : K[X], ∃ quadraticBad : Finset K,
      linearE ≠ 0 ∧ linearE.natDegree ≤ 26854534485 ∧
      quadraticE ≠ 0 ∧ quadraticE.natDegree ≤ 114687 ∧
      quadraticBad.card ≤ 936616 ∧
      (LinearMessageFamily.family (parent c1 c2)).card ≤ 111 ∧
      (LinearMessageFamily.sparseChallenges (parent c1 c2) Gamma).card ≤ 3108 ∧
      ∀ (d : Data (K := K)) gamma Q,
        gamma ∈ Gamma → Root c1 c2 d gamma Q →
        Outcome c1 c2 Gamma linearE quadraticE quadraticBad d gamma Q := by
  obtain ⟨linearE, linearNonzero, linearDegree, familyCard, sparseCard, linearCover⟩ :=
    SelectedLinearCover.exists_selected_classification c1 c2 Gamma
  obtain ⟨quadraticE, quadraticBad, quadraticNonzero, quadraticDegree, badCard, quadraticCover⟩ :=
    SelectedQuadraticCover.fixed_cover c1 c2
  refine ⟨linearE, quadraticE, quadraticBad, linearNonzero, linearDegree,
    quadraticNonzero, quadraticDegree, badCard, familyCard, sparseCard, ?_⟩
  intro d gamma Q member root
  rcases linearCover d gamma Q member root with linearHit | sparse | higher | messages
  · exact Or.inl linearHit
  · exact Or.inr (Or.inl sparse)
  · have reduced := Generic.refine_higher (parent c1 c2) quadraticE quadraticBad
      (point d) (fun r => CurveOODGate.answerCurve (answers d r)) gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original Q))
      (quadraticCover (point d) (fun r => CurveOODGate.answerCurve (answers d r)) gamma
        (exactCircleGRSPolynomial ((atGamma d gamma).original Q))) higher
    rcases reduced with quadraticHit | quadraticException | cubic
    · exact Or.inr (Or.inr (Or.inl quadraticHit))
    · exact Or.inr (Or.inr (Or.inr (Or.inl quadraticException)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl cubic))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr messages))))

#print axioms exists_selected_reduction
end
end AspisV8.SelectedQuadraticReduction
