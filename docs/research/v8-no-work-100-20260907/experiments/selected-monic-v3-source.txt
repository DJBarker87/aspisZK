import MonicFactorOOD
import SelectedIdentityCover

/-! Same-Q selected interface for the monic linear-factor classification.
The obstruction polynomial depends only on pre-OOD C1/C2.  Its roots at
both actual GRS OOD points are retained as an event, not assigned an
unsupported source/Fiat-Shamir sampling probability. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000
namespace AspisV8.SelectedMonicCover
namespace Generic
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV8.FactorIdentityCover AspisV8.MonicFactorOOD
noncomputable section
variable {K : Type*} [Field K]

/-- Construct the nested factor/candidate result generically. The concrete
QM31 caller only instantiates it once, avoiding expansion of its field tower. -/
theorem refine_root (degree : Nat) (P : TrivariatePolynomial K) (E : K[X])
    (control : ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X])
      (F : TrivariatePolynomial K), F ∈ curvePrimeFactors P →
      F.Monic → F.natDegree = 1 → Retained points answers F →
      (∀ r, (answers r).natDegree ≤ degree) →
      (rootCurve F).natDegree ≤ degree ∨ ∀ r, E.eval (points r) = 0)
    (points : Fin 2 → K) (answers : Fin 2 → K[X])
    (bounds : ∀ r, (answers r).natDegree ≤ degree) (gamma : K) (U : K[X])
    (root : ∃ F ∈ curvePrimeFactors P, Retained points answers F ∧
      challengeCandidateHom gamma U F = 0) :
    (∃ F ∈ curvePrimeFactors P, Retained points answers F ∧
      challengeCandidateHom gamma U F = 0 ∧
      (¬(F.Monic ∧ F.natDegree = 1) ∨
        (rootCurve F).natDegree ≤ degree ∧ U = (rootCurve F).eval (C gamma))) ∨
      ∀ r, E.eval (points r) = 0 := by
  classical
  obtain ⟨F, member, retained, candidate⟩ := root
  by_cases linear : F.Monic ∧ F.natDegree = 1
  · rcases control points answers F member linear.1 linear.2 retained bounds with small | bad
    · exact Or.inl ⟨F, member, retained, candidate, Or.inr
        ⟨small, candidate_eq_curve F linear.1 linear.2 gamma U candidate⟩⟩
    · exact Or.inr bad
  · exact Or.inl ⟨F, member, retained, candidate, Or.inl linear⟩
end
end Generic

open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.SelectedFactorCoherence AspisV8.SelectedIdentityCover
open AspisV8.FactorIdentityCover AspisV8.MonicFactorOOD
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisK1.V7Tag73ExactGRSConversion
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

theorem parent_x_degree (c1 : C1Received) (c2 : C2Received) :
    (trivariateXOuterEquiv K (parent c1 c2)).natDegree ≤ 114687 := by
  exact Nat.le_of_lt_succ (curveTrivariatePolynomial_xNatDegree_lt
    (by norm_num : 0 < 114688) (fixedInterpolant c1 c2))

/-- No arbitrary-degree or non-monic branch is dropped. Even the small
polynomial curve is not yet an original-code tuple or a payment witness. -/
def Classified (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (gamma : K) (Q : Fin 1024 → K) : Prop :=
  ∃ F ∈ curvePrimeFactors (parent c1 c2),
    Retained (point d) (fun r => CurveOODGate.answerCurve (answers d r)) F ∧
    challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) F = 0 ∧
    (¬ (F.Monic ∧ F.natDegree = 1) ∨
      (rootCurve F).natDegree ≤ 28 ∧
        exactCircleGRSPolynomial ((atGamma d gamma).original Q) =
          (rootCurve F).eval (C gamma))

theorem exists_selected_classification (c1 : C1Received) (c2 : C2Received) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 114687 ∧
      ∀ (d : Data (K := K)) gamma Q,
        Root c1 c2 d gamma Q →
        Classified c1 c2 d gamma Q ∨ ∀ r, E.eval (point d r) = 0 := by
  obtain ⟨E, nonzero, bound, obstruction⟩ :=
    exists_parent_ood_obstruction 28 (parent c1 c2)
      (curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2))
  refine ⟨E, nonzero, bound.trans (parent_x_degree c1 c2), ?_⟩
  intro d gamma Q root
  exact Generic.refine_root 28 (parent c1 c2) E obstruction (point d)
    (fun r => CurveOODGate.answerCurve (answers d r)) (answers_degree d) gamma
    (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) root

#print axioms Generic.refine_root
#print axioms parent_x_degree
#print axioms exists_selected_classification
end
end AspisV8.SelectedMonicCover
