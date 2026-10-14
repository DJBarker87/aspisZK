import R1NaturalPairInverse
import R1FractionalLiftInvolution

/-! Exact parity extraction and fixed inverse for the cleared circle
numerator. No expansion of the 512-term lift is used. -/

set_option autoImplicit false

namespace AspisR1.CircleNumeratorInverse

open Polynomial
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriCoherentCandidateExtraction
open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.NaturalPairInverse
open AspisV5FriCircleEncoderDistance
open AspisCircleGroupOrder

noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

def evenPart (q : K[X]) : K[X] :=
  monomialPolynomial (fun i : Fin 513 => q.coeff (2 * i.val))

def oddPart (q : K[X]) : K[X] :=
  monomialPolynomial (fun i : Fin 512 => (2 : K)⁻¹ * q.coeff (2 * i.val + 1))

theorem evenPart_circleNumerator (p0 p1 : K[X]) :
    evenPart (circleNumerator p0 p1) = fractionalLift 512 p0 := by
  have hcoeff (n : Nat) :
      (circleNumerator p0 p1).coeff (2 * n) = (fractionalLift 512 p0).coeff n := by
    unfold circleNumerator
    rw [Polynomial.coeff_add, mobiusLift_eq_expand 512 p0, coeff_expand_two_even,
      mobiusLift_eq_expand 511 p1, coeff_scaledX_expand_two_even]
    simp
  ext n
  by_cases hn : n < 513
  · change (monomialPolynomial _).coeff n = (fractionalLift 512 p0).coeff n
    rw [monomialPolynomial_coeff _ ⟨n, hn⟩]
    exact hcoeff n
  · rw [evenPart, monomialPolynomial_coeff_eq_zero_of_ge _ n (by omega)]
    have hd : (fractionalLift 512 p0).natDegree ≤ 512 :=
      fractionalLift_natDegree_le 512 p0
    have hcoeffzero : (fractionalLift 512 p0).coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hd (by omega))
    rw [hcoeffzero]

theorem oddPart_circleNumerator (p0 p1 : K[X]) :
    oddPart (circleNumerator p0 p1) = fractionalLift 511 p1 := by
  have hcoeff (n : Nat) :
      (2 : K)⁻¹ * (circleNumerator p0 p1).coeff (2 * n + 1) =
        (fractionalLift 511 p1).coeff n := by
    unfold circleNumerator
    rw [Polynomial.coeff_add, mobiusLift_eq_expand 512 p0, coeff_expand_two_odd,
      mobiusLift_eq_expand 511 p1, coeff_scaledX_expand_two_odd]
    simp [NeZero.ne (2 : K)]
  ext n
  by_cases hn : n < 512
  · change (monomialPolynomial _).coeff n = (fractionalLift 511 p1).coeff n
    rw [monomialPolynomial_coeff _ ⟨n, hn⟩]
    exact hcoeff n
  · rw [oddPart, monomialPolynomial_coeff_eq_zero_of_ge _ n (by omega)]
    have hd : (fractionalLift 511 p1).natDegree ≤ 511 :=
      fractionalLift_natDegree_le 511 p1
    have hcoeffzero : (fractionalLift 511 p1).coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hd (by omega))
    rw [hcoeffzero]

def decoded (q : K[X]) : InitialMessage K :=
  NaturalPairInverse.pair (inverseLift 512 (evenPart q))
    (inverseLift 511 (oddPart q))

theorem initialP0_decoded (q : K[X]) :
    initialP0 (decoded q) =
      AspisR0.PolynomialPair.truncate (inverseLift 512 (evenPart q)) := by
  exact NaturalPairInverse.initialP0_pair _ _

theorem initialP1_decoded (q : K[X]) :
    initialP1 (decoded q) =
      AspisR0.PolynomialPair.truncate (inverseLift 511 (oddPart q)) := by
  exact NaturalPairInverse.initialP1_pair _ _

theorem decoded_circleNumerator (m : Coeff0 K) :
    decoded (circleNumerator (initialP0 m) (initialP1 m)) = m := by
  have hcard := m31_extension_card_gt_513 (K := K)
  have hbound0 : (initialP0 m).natDegree ≤ 511 := by
    have h := initialP0_degree_lt m
    omega
  have hbound1 : (initialP1 m).natDegree ≤ 511 := by
    have h := initialP1_degree_lt m
    omega
  have hinv0 : inverseLift 512 (evenPart
      (circleNumerator (initialP0 m) (initialP1 m))) = initialP0 m := by
    rw [evenPart_circleNumerator]
    exact inverseLift_lift 512 (by omega) (initialP0 m) (by omega)
  have hinv1 : inverseLift 511 (oddPart
      (circleNumerator (initialP0 m) (initialP1 m))) = initialP1 m := by
    rw [oddPart_circleNumerator]
    exact inverseLift_lift 511 (by omega) (initialP1 m) (by omega)
  have h0 : initialP0 (decoded (circleNumerator (initialP0 m) (initialP1 m))) = initialP0 m := by
    rw [initialP0_decoded, hinv0]
    exact AspisR0.PolynomialPair.truncate_eq _ hbound0
  have h1 : initialP1 (decoded (circleNumerator (initialP0 m) (initialP1 m))) = initialP1 m := by
    rw [initialP1_decoded, hinv1]
    exact AspisR0.PolynomialPair.truncate_eq _ hbound1
  have hpair : (initialP0 (decoded (circleNumerator (initialP0 m) (initialP1 m))),
      initialP1 (decoded (circleNumerator (initialP0 m) (initialP1 m)))) =
      (initialP0 m, initialP1 m) := congrArg₂ Prod.mk h0 h1
  exact initialPolynomialPair_injective hpair

def imageTest (q : K[X]) : Prop :=
  circleNumerator (initialP0 (decoded q)) (initialP1 (decoded q)) = q

theorem imageTest_iff (q : K[X]) :
    imageTest q ↔ ∃ m : Coeff0 K,
      circleNumerator (initialP0 m) (initialP1 m) = q := by
  constructor
  · intro h
    exact ⟨decoded q, h⟩
  · rintro ⟨m, hm⟩
    change circleNumerator (initialP0 (decoded q)) (initialP1 (decoded q)) = q
    rw [← hm, decoded_circleNumerator]

#print axioms evenPart_circleNumerator
#print axioms oddPart_circleNumerator
#print axioms initialP0_decoded
#print axioms initialP1_decoded
#print axioms decoded_circleNumerator
#print axioms imageTest_iff

end
end AspisR1.CircleNumeratorInverse
