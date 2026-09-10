import GammaConstantLinear
import SelectedLinearFactorRecovery

/-! Removes the supplied rational-root premise in the gamma-constant
denominator class. This is a same-factor, actual source-message result,
not an own-support or payment-witness theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedGammaConstantRecovery
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.SelectedGRSSubmodule AspisV8.SelectedLinearFactorRecovery
open AspisV8.GammaConstantLinear
noncomputable section

def MessageCover (F : TrivariatePolynomial K) (messages : Fin 29 → Message) : Prop :=
  ∀ gamma (U : K[X]), challengeCandidateHom gamma U F = 0 →
    U = exactCircleGRSPolynomial (∑ j : Fin 29, gamma^j.val • messages j)

/-- Both branches are fixed from F and Gamma, before the particular actual
gamma or a candidate chosen after alpha. In the dense branch the SAME tuple
covers every later polynomial root, not only the interpolation nodes. -/
theorem actual_message_dichotomy (P F : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (linear : F.natDegree = 1)
    (constant : (F.coeff 1).natDegree = 0)
    (small : (F.coeff 0).natDegree ≤ 28) (Gamma : Finset K) :
    (goodChallenges F Gamma).card ≤ 28 ∨
      ∃ messages : Fin 29 → Message, MessageCover F messages := by
  have equation := rationalRoot_equation (F.coeff 1) (F.coeff 0) constant
    (leading_coefficient_ne_zero F linear)
  rcases SelectedLinearFactorRecovery.actual_message_dichotomy P F nonzero member linear
    (rationalRoot (F.coeff 1) (F.coeff 0))
    ((rationalRoot_degree (F.coeff 1) (F.coeff 0)).trans small) equation Gamma with
    sparse | dense
  · exact Or.inl sparse
  · obtain ⟨messages, coefficients, cover⟩ := dense
    exact Or.inr ⟨messages, cover⟩

#print axioms actual_message_dichotomy
end
end AspisV8.SelectedGammaConstantRecovery
