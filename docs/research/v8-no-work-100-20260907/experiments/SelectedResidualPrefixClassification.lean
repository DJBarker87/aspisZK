import SelectedMiddleImageRecovery

/-! Source-review draft: discharge CandidateClassifies from the actual
C1/C2 auxiliary parent. E and the tuple family precede BOTH OOD points;
the shared beta follows the OOD data but precedes gamma and every later
Q/final choice. This is an algebraic prefix bridge, not construction of an
authenticated Execution from a parsed Rust transcript. No new recovery or
probability theorem, and no package-wide source replay, is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedResidualPrefixClassification
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.FactorIdentityCover
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Tuple := Fin 29 → Fin 1024 → K
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

namespace Generic

/-- A named predicate at the abstract-P boundary keeps the large concrete
source parent out of the proof of the reused classification theorem. -/
def RowPlan (P : TrivariatePolynomial K) (Gamma : Finset K) (E : K[X]) : Prop :=
  ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X]),
    (∀ r, (answers r).natDegree ≤ 28) →
    ∃ beta : K[X], beta ≠ 0 ∧ beta.natDegree ≤ 40 ∧
      ∀ (gamma : K) (message : SelectedGRSSubmodule.Message), gamma ∈ Gamma →
        challengeCandidateHom gamma (exactCircleGRSPolynomial message) P=0 →
        (∀ r, (exactCircleGRSPolynomial message).eval (points r)=
          (answers r).eval gamma) →
        beta.eval gamma=0 ∨ (∀ r, E.eval (points r)=0) ∨
          gamma ∈ LinearMessageFamily.sparseChallenges P Gamma ∨
          ∃ p ∈ LinearMessageFamily.family P, message=ClaimTransport.batch gamma p

/-- The full quantifier order is inherited literally from the checked
linear-parent theorem. This does not choose a post-transcript plan. -/
theorem exists_row_plan (P : TrivariatePolynomial K) (nonzero : P ≠ 0)
    (yDegree : P.natDegree ≤ 1)
    (xDegree : (trivariateXOuterEquiv K P).natDegree ≤ 803229)
    (weight : trivariateYZWeight 28 P ≤ 40) (Gamma : Finset K) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 65061549 ∧
      (LinearMessageFamily.family P).card ≤ 1 ∧
      (LinearMessageFamily.sparseChallenges P Gamma).card ≤ 28 ∧
      RowPlan P Gamma E :=
  MiddleLinearClassification.exists_classification P nonzero yDegree xDegree weight Gamma
end Generic

open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.GammaComponentGame AspisV8.SelectedOODGate AspisV8.CurveOODGate
open AspisV8.SelectedMiddleImageRecovery
open AspisV8.OODInterpolant

/-- This family depends only on the actual C1/C2 auxiliary parent, not on
gamma, either OOD point, answers, or the final selected after alpha. -/
def family (c1 : C1Received) (c2 : C2Received) : Finset Tuple :=
  LinearMessageFamily.family (SelectedMiddleSimpleParent.parent c1 c2)

def sparseSource (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K) : Finset K :=
  LinearMessageFamily.sparseChallenges (SelectedMiddleSimpleParent.parent c1 c2) Gamma

/-- Actual stored-point and 29-lane answer-curve substitutions. This is
valid for arbitrary Data; its image/circle checks are needed later to feed
actual Q candidates into the classifier, not to construct the classifier.
No future gamma/final is an input to beta's existential choice. -/
theorem row_plan_candidate (c1 : C1Received) (c2 : C2Received)
    (Gamma : Finset K) (E : K[X])
    (plan : Generic.RowPlan (SelectedMiddleSimpleParent.parent c1 c2) Gamma E)
    (d : Data (K := K)) :
    ∃ beta : K[X], beta ≠ 0 ∧ beta.natDegree ≤ 40 ∧
      CandidateClassifies c1 c2 Gamma (family c1 c2) E beta (sparseSource c1 c2 Gamma) d := by
  obtain ⟨beta, nonzero, degree, classify⟩ := plan (point d)
    (fun r => answerCurve (answers d r)) (fun r => answerCurve_degree _)
  refine ⟨beta, nonzero, degree, ?_⟩
  exact classify

/-- Discharge the classifier/family/sparse hypotheses in the residual
closure for the actual selected parent. E is fixed before universal d;
beta is fixed before all gamma/message/Q continuations. This does not
assume earlyC1 success, received polynomiality, or candidate membership.
Prefix authentication and a causal construction of Execution are separate.
-/
theorem exists_source_classifier (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 65061549 ∧
      (family c1 c2).card ≤ 1 ∧ (sparseSource c1 c2 Gamma).card ≤ 28 ∧
      ∀ d : Data (K := K), ∃ beta : K[X], beta ≠ 0 ∧ beta.natDegree ≤ 40 ∧
        CandidateClassifies c1 c2 Gamma (family c1 c2) E beta
          (sparseSource c1 c2 Gamma) d := by
  have bounds := SelectedMiddleSimpleParent.parent_bounds c1 c2
  obtain ⟨E, nonzero, degree, one, sparseSmall, plan⟩ := Generic.exists_row_plan
    (SelectedMiddleSimpleParent.parent c1 c2) (SelectedMiddleSimpleParent.parent_nonzero c1 c2)
    bounds.1 bounds.2.1 bounds.2.2 Gamma
  refine ⟨E, nonzero, degree, one, sparseSmall, ?_⟩
  intro d
  exact row_plan_candidate c1 c2 Gamma E plan d

#print axioms Generic.exists_row_plan
#print axioms row_plan_candidate
#print axioms exists_source_classifier
end
end AspisV8.SelectedResidualPrefixClassification
