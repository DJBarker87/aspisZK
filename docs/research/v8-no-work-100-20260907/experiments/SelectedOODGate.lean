import CurveOODGate
import CoveredOriginalSymbols
import CoveredOODGRS
import AspisFormal.K1.V7ExactCorrelatedAgreement

/-! New gamma-level reduction for the literal selected arbitrary word.
An image-valid covered quotient yields a root of the fixed pre-OOD curve
interpolant and satisfies both actual normalized OOD answer polynomials.
If either substitution is not an identity, at most117077 gammas qualify.
Both identities are retained as the unresolved branch; neither identity is
component membership or checked payment extraction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000
namespace AspisV8.SelectedOODGate
open Polynomial Finset
open AspisV8.SelectedReceivedOracle AspisV8.EarlyC1Projection
open AspisV8.EarlyC1LateProjection AspisV8.OODInterpolant
open AspisV8.GammaComponentGame AspisV8.CoveredOriginalSymbols
open AspisV8.ComponentOODBinding AspisV8.CoveredOODGRS
open AspisV8.QuotientFamilySelected AspisV8.CurveOODGate
open AspisK1.V7ExactCorrelatedAgreement
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7Tag73ExactMultiplicityThreeGS
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Coefficients := CurveMonomialIndex 1024 28 initialCurveXBound
  initialCurveYRows initialCurveZBound → K

theorem lastRow : 1024*111≤114687 := by norm_num

/-- Chosen from C1 and C2 alone, before either OOD challenge/answer. This
huge finite linear-system existence object is NOT an executable extractor. -/
def fixedInterpolant (c1 : C1Received) (c2 : C2Received) : Coefficients :=
  Classical.choose (exists_exactInitialCurveInterpolation (received29 c1 c2))

theorem fixedInterpolant_nonzero (c1 : C1Received) (c2 : C2Received) :
    fixedInterpolant c1 c2≠0 :=
  (Classical.choose_spec (exists_exactInitialCurveInterpolation (received29 c1 c2))).1

theorem fixedInterpolant_kernel (c1 : C1Received) (c2 : C2Received) :
    curveInterpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedLanes (received29 c1 c2)) (fixedInterpolant c1 c2)=0 :=
  (Classical.choose_spec (exists_exactInitialCurveInterpolation (received29 c1 c2))).2

def point (d : Data (K := K)) (r : Fin 2) : K := pointY d r/(1+pointX d r)
def factor (d : Data (K := K)) (r : Fin 2) : K := (1+(point d r)^2)^512
def answers (d : Data (K := K)) (r : Fin 2) (lane : Fin 29) : K :=
  factor d r*d.answers r lane
def gate (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (r : Fin 2) : K[X] :=
  atPoint (fixedInterpolant c1 c2) (point d r) (answers d r)

/-- All29 gamma powers remain, after multiplying by the correct GRS
clearing factor. This is not the quadratic helper curve. -/
theorem answers_eval (d : Data (K := K)) (gamma : K) (r : Fin 2) :
    (answerCurve (answers d r)).eval gamma=factor d r*(atGamma d gamma).batch r := by
  rw [answerCurve,receivedCurvePolynomial_eval]
  simp only [answers,Data.batch,atGamma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lane _
  ring

theorem answers_degree (d : Data (K := K)) (r : Fin 2) :
    (answerCurve (answers d r)).natDegree≤28 := answerCurve_degree (answers d r)

theorem gate_degree (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (r : Fin 2) :
    (gate c1 c2 d r).natDegree≤117077 := by
  have strict := atPoint_degree (by norm_num : 0<117078)
    (fixedInterpolant c1 c2) (point d r) (answers d r)
  exact Nat.le_of_lt_succ strict

/-- The same Q supplies both the original-code agreement and the OOD
equalities. Q can be chosen after gamma/alpha; no candidate-family union. -/
theorem covered_compatible (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, pointX d r≠-1) (gamma : K) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (member : Q∈literalFamily (SelectedComponentGame.received c1 c2 d gamma)) :
    compatible lastRow (fixedInterpolant c1 c2) (point d) (answers d) gamma := by
  let strategy := originalStrategy c1 c2 d (fun _ => Q)
  have valid := selected_width29_valid c1 c2 d checked (fun _ => Q) gamma image member
  have root := exactInitialValidCandidate_substitute_eq_zero (received29 c1 c2)
    strategy (fixedInterpolant c1 c2) (fixedInterpolant_kernel c1 c2) gamma valid
  refine ⟨exactCircleGRSPolynomial ((atGamma d gamma).original Q),root,?_⟩
  intro r
  rw [answers_eval]
  simpa only [point,factor,pointX,pointY,atGamma] using
    original_grs_at_ood (atGamma d gamma) checked Q image circles r (west r)

theorem covered_gate_zero (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, pointX d r≠-1) (gamma : K) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (member : Q∈literalFamily (SelectedComponentGame.received c1 c2 d gamma)) (r : Fin 2) :
    (gate c1 c2 d r).eval gamma=0 := by
  obtain ⟨candidate,root,points⟩ := covered_compatible c1 c2 d checked circles west
    gamma Q image member
  exact atPoint_zero_of_candidate lastRow (fixedInterpolant c1 c2) (point d r)
    (answers d r) gamma candidate root (points r)

/-- Uniform over every later choice. The retained identity/identity case is
defined by the fixed words, actual OOD points and both actual answer rows,
not by a chosen provider's success/failure or a post-gamma target. -/
theorem covered_gamma_card_le (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, pointX d r≠-1) (S : Finset K)
    (nonidentity : ∃ r, gate c1 c2 d r≠0)
    (covered : ∀ gamma∈S, ∃ Q∈literalFamily (SelectedComponentGame.received c1 c2 d gamma),
      Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0) : S.card≤117077 := by
  apply compatible_card_le lastRow (by norm_num : 0<117078)
    (fixedInterpolant c1 c2) (point d) (answers d) S nonidentity
  intro gamma member
  obtain ⟨Q,qmember,image⟩ := covered gamma member
  exact covered_compatible c1 c2 d checked circles west gamma Q image qmember

#print axioms fixedInterpolant_nonzero
#print axioms fixedInterpolant_kernel
#print axioms answers_eval
#print axioms answers_degree
#print axioms gate_degree
#print axioms covered_compatible
#print axioms covered_gate_zero
#print axioms covered_gamma_card_le
end
end AspisV8.SelectedOODGate
