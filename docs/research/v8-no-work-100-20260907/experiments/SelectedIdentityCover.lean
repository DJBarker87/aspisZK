import FactorIdentityCover
import SelectedFactorCoherence

/-! The new factor-family cover for the SAME selected received-word
execution, not a supplied tuple or exact-polynomial received oracle. Includes
all symbolic OOD/singular/repeated-parent cases. The retained factor root is
still NOT a recovered original-component tuple or a checked payment witness.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000
namespace AspisV8.SelectedIdentityCover
open Polynomial Finset
open AspisV8.FactorCoherence AspisV8.FactorIdentityCover
open AspisV8.SelectedFactorCoherence AspisV8.SelectedOODGate
open AspisV8.SelectedReceivedOracle AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.ComponentOODBinding AspisV8.GammaComponentGame AspisV8.OODInterpolant
open AspisV8.QuotientFamilySelected AspisV8.CurveOODGate
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7Tag73ExactGRSConversion
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

def Root (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (gamma : K) (Q : Fin 1024 → K) : Prop :=
  ∃ F∈curvePrimeFactors (parent c1 c2),
    Retained (point d) (fun r => answerCurve (answers d r)) F ∧
      challengeCandidateHom gamma (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) F=0

/-- The code/GRS root and both OOD evaluations are proved for one literal
reconstruction of Q. Post-alpha selection is unrestricted. -/
theorem literal_candidate
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, pointX d r≠-1) (gamma : K) (Q : Fin 1024 → K)
    (member : Q∈literalFamily (SelectedComponentGame.received c1 c2 d gamma))
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0) :
    challengeCandidateHom gamma (exactCircleGRSPolynomial ((atGamma d gamma).original Q))
        (parent c1 c2)=0 ∧
      ∀ r, (exactCircleGRSPolynomial ((atGamma d gamma).original Q)).eval (point d r)=
        (answerCurve (answers d r)).eval gamma := by
  constructor
  · have valid := CoveredOriginalSymbols.selected_width29_valid c1 c2 d checked
      (fun _ => Q) gamma image member
    have root := AspisK1.V7ExactCorrelatedAgreement.exactInitialValidCandidate_substitute_eq_zero
      (received29 c1 c2) (CoveredOriginalSymbols.originalStrategy c1 c2 d (fun _ => Q))
      (fixedInterpolant c1 c2) (fixedInterpolant_kernel c1 c2) gamma valid
    exact candidate_root lastRow (fixedInterpolant c1 c2) gamma _ root
  · intro r
    rw [answers_eval]
    simpa only [point,SelectedOODGate.factor,pointX,pointY,atGamma] using
      CoveredOODGRS.original_grs_at_ood (atGamma d gamma) checked Q image circles r (west r)

/-- One exception polynomial is fixed before gamma. Both actual sequential
OOD rows participate. The Y-constant content and all discarded factors are
charged within ONE117077 degree budget, including repeated/singular parents.
No zero-specialization term, derivative term, or factor-count multiplier is
added on top of this theorem. -/
theorem exists_selected_cover (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) :
    ∃ exception : K[X], exception≠0 ∧ exception.natDegree≤117077 ∧
      ∀ (checked : d.Checked)
        (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
        (west : ∀ r, pointX d r≠-1) (gamma : K) (Q : Fin 1024 → K),
        Q∈literalFamily (SelectedComponentGame.received c1 c2 d gamma) →
        (Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0) →
        exception.eval gamma=0 ∨ Root c1 c2 d gamma Q := by
  have nonzero : parent c1 c2≠0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  obtain ⟨exception,nonzeroException,degree,covered⟩ := exists_identity_factor_cover 28
    (parent c1 c2) nonzero (point d) (fun r => answerCurve (answers d r))
    (fun r => answerCurve_degree _)
  refine ⟨exception,nonzeroException,?_,?_⟩
  · have bound := trivariateYZWeight_curveTrivariatePolynomial_lt
      (by norm_num : 0<117078) (fixedInterpolant c1 c2)
    exact degree.trans (Nat.le_of_lt_succ bound)
  · intro checked circles west gamma Q member image
    obtain ⟨root,points⟩ := literal_candidate c1 c2 d checked circles west gamma Q member image
    exact covered gamma _ root points

#print axioms literal_candidate
#print axioms exists_selected_cover
end
end AspisV8.SelectedIdentityCover
