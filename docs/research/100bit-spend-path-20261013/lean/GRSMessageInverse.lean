import R1CircleNumeratorInverse
import Wide.GRSConversion

/-! The released GRS message polynomial agrees with the cleared circle
numerator, so the existing exact polynomial inverse and image test transfer
through the GRS conversion. This is an algebraic specification only. -/

set_option autoImplicit false

namespace AspisR1.GRSMessageInverse

open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GRSConversion
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity

noncomputable section
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K]

def inverse (q : K[X]) : InitialMessage K :=
  AspisR1.CircleNumeratorInverse.decoded q

theorem inverse_messagePolynomial (m : InitialMessage K) :
    inverse ((exactInitialGRSConversion (K := K)).messagePolynomial m) = m := by
  change AspisR1.CircleNumeratorInverse.decoded (exactCircleGRSPolynomial m) = m
  rw [exactCircleGRSPolynomial_eq_released]
  exact AspisR1.CircleNumeratorInverse.decoded_circleNumerator m

theorem messagePolynomial_inverse_iff (q : K[X]) :
    (exactInitialGRSConversion (K := K)).messagePolynomial (inverse q) = q ↔
      ∃ m : InitialMessage K,
        (exactInitialGRSConversion (K := K)).messagePolynomial m = q := by
  change exactCircleGRSPolynomial (inverse q) = q ↔
    ∃ m : InitialMessage K, exactCircleGRSPolynomial m = q
  simp_rw [exactCircleGRSPolynomial_eq_released]
  exact AspisR1.CircleNumeratorInverse.imageTest_iff q

#print axioms inverse_messagePolynomial
#print axioms messagePolynomial_inverse_iff

end
end AspisR1.GRSMessageInverse
