import MiddleSimpleRootV7
import SelectedRegularLowSupport

/-! A second, analysis-only parent tailored to the literal middle-support
threshold. It is chosen from C1/C2 before OOD. The old parent and its actual
higher-factor event remain unchanged; a later consumer may intersect them.
No decoder, received-word polynomiality, early-C1 outcome, or pre-alpha
candidate choice is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedMiddleSimpleParent
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7ExactCorrelatedAgreement
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.SelectedReceivedOracle AspisV8.GammaComponentGame
open AspisV8.OODInterpolant AspisV8.SelectedHigherYRegularTail
open AspisV8.SelectedRegularLowSupport
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def coefficients (c1 : C1Received) (c2 : C2Received) : MiddleSimpleRoot.Coefficients K :=
  Classical.choose (MiddleSimpleInterpolation.exists_middle_interpolant
    exactInitialGRSConversion.points (exactInitialNormalizedLanes (received29 c1 c2)))

theorem coefficients_nonzero (c1 : C1Received) (c2 : C2Received) :
    coefficients c1 c2 ≠ 0 :=
  (Classical.choose_spec (MiddleSimpleInterpolation.exists_middle_interpolant
    exactInitialGRSConversion.points (exactInitialNormalizedLanes (received29 c1 c2)))).1

theorem coefficients_kernel (c1 : C1Received) (c2 : C2Received) :
    MiddleSimpleInterpolation.simpleMap exactInitialGRSConversion.points
      (exactInitialNormalizedLanes (received29 c1 c2)) (coefficients c1 c2) = 0 :=
  (Classical.choose_spec (MiddleSimpleInterpolation.exists_middle_interpolant
    exactInitialGRSConversion.points (exactInitialNormalizedLanes (received29 c1 c2)))).2

def parent (c1 : C1Received) (c2 : C2Received) : TrivariatePolynomial K :=
  curveTrivariatePolynomial (coefficients c1 c2)

theorem parent_nonzero (c1 : C1Received) (c2 : C2Received) : parent c1 c2 ≠ 0 :=
  MiddleSimpleRoot.parent_nonzero (coefficients c1 c2) (coefficients_nonzero c1 c2)

theorem parent_bounds (c1 : C1Received) (c2 : C2Received) :
    (parent c1 c2).natDegree ≤ 1 ∧
      (trivariateXOuterEquiv K (parent c1 c2)).natDegree ≤ 803229 ∧
      trivariateYZWeight 28 (parent c1 c2) ≤ 40 :=
  ⟨MiddleSimpleRoot.parent_y_degree (coefficients c1 c2),
    MiddleSimpleRoot.parent_x_degree (coefficients c1 c2),
    MiddleSimpleRoot.parent_yz_weight (coefficients c1 c2)⟩

/-- Exact original-message support: four symbols per full fibre, losing
at most two chord-pole symbols. The support belongs to this SAME Q. -/
theorem middle_original_support (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked) (gamma : K) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (middle : 200808 ≤ fibreCount (SelectedComponentGame.received c1 c2 d gamma) Q) :
    803230 ≤ (originalSupport c1 c2 d gamma Q).card := by
  have symbols := fibre_to_original_support c1 c2 d checked gamma Q image
  omega

/-- Literal selected encoder/normalization bridge. In particular Q may be
the actual post-alpha final witness; no continuity or polynomial gamma
dependence is imposed on it. -/
theorem candidate_root (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked) (gamma : K) (Q : Fin 1024 → K)
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (middle : 200808 ≤ fibreCount (SelectedComponentGame.received c1 c2 d gamma) Q) :
    challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) (parent c1 c2) = 0 := by
  apply MiddleSimpleRoot.middle_root exactInitialGRSConversion.points
    exactInitialGRSConversion.points_injective
    (exactInitialNormalizedLanes (received29 c1 c2)) (coefficients c1 c2)
    (coefficients_kernel c1 c2) gamma
    (exactCircleGRSPolynomial ((atGamma d gamma).original Q))
    (originalSupport c1 c2 d gamma Q)
    (exactCircleGRSPolynomial_degree_le _)
    (middle_original_support c1 c2 d checked gamma Q image middle)
  intro i member
  exact HigherYRegularBranch.normalized_agreement (received29 c1 c2)
    ((atGamma d gamma).original Q) gamma i
    (originalSupport_agreement c1 c2 d gamma Q i member)

#print axioms coefficients_nonzero
#print axioms coefficients_kernel
#print axioms parent_nonzero
#print axioms parent_bounds
#print axioms middle_original_support
#print axioms candidate_root
end
end AspisV8.SelectedMiddleSimpleParent
