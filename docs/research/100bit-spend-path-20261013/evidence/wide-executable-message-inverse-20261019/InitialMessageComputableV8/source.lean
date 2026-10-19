import WideExactInitialMessageComputableV4
import WideExactInitialInverseBridgeV2

import WideExactInitialCirclePairInverseV5
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V5FriConcreteEncoderApplicability
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Univariate.ToPoly.Degree

set_option autoImplicit false
namespace AspisWide.InitialMessageComputableV5
open CompPoly Polynomial
open AspisWide.InitialParityCBridgeV9
open AspisWide.InitialInverseComputable
open AspisWide.InitialInverse
open AspisWide.NaturalBasisTriangularV4
open AspisWide.InitialCirclePairInverse
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisCircleTensorBinding
open AspisV5FriCircleEncoderDistance

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K]

def evenV (m : Fin 1024 → K) : Fin 512 → K := fun i => m ⟨2 * i.val, by omega⟩
def oddV (m : Fin 1024 → K) : Fin 512 → K := fun i => m ⟨2 * i.val + 1, by omega⟩

theorem encode_toPoly_basisSum : ∀ n (c : Fin (n + 1) → K),
    (encode (K := K) n c).toPoly =
      ∑ i : Fin (n + 1), C (c i) * naturalLinePoly K i.val := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [encode, basis_toPoly, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly]
  | succ n ih =>
      intro c
      rw [encode, CompPoly.CPolynomial.toPoly_add, ih,
        CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly,
        basis_toPoly]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]

theorem naturalPolynomial_encode (c : Fin 512 → K) :
    (encode (K := K) 511 c).toPoly = naturalCoefficientPolynomial c := by
  rw [encode_toPoly_basisSum]
  exact (naturalCoefficientPolynomial_eq_basisSum (K := K) (n := 512)
    (by omega) c).symm

theorem evenV_initial (m : Fin 1024 → K) :
    initialP0 m = naturalCoefficientPolynomial (evenV m) := by
  rfl

theorem oddV_initial (m : Fin 1024 → K) :
    initialP1 m = naturalCoefficientPolynomial (oddV m) := by
  rfl

theorem decodeMessage_of_circleNumerator
    (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (hinj0 : Function.Injective nodes0) (hinj1 : Function.Injective nodes1)
    (havoid0 : ∀ i, nodes0 i ≠ -1) (havoid1 : ∀ i, nodes1 i ≠ -1)
    (q : CPolynomial K) (m : Fin 1024 → K)
    (hinput : q.toPoly = circleNumerator (initialP0 m) (initialP1 m)) :
    AspisWide.InitialMessageComputableV1.decodeMessage nodes0 nodes1 q = m := by
  have heven : (evenC q).toPoly = fractionalLift 512 (initialP0 m) := by
    have hcoeff : ∀ n, (evenC q).toPoly.coeff n =
        (evenPart q.toPoly).coeff n := by
      intro n
      rw [evenC_coeff]
      by_cases hn : n < 513
      · simp only [if_pos hn]
        exact (monomialPolynomial_coeff
          (fun i : Fin 513 => q.toPoly.coeff (2 * i.val)) ⟨n, hn⟩).symm
      · simp only [if_neg hn]
        have hz := monomialPolynomial_coeff_eq_zero_of_ge
          (fun i : Fin 513 => q.toPoly.coeff (2 * i.val)) n (by omega)
        simpa [evenPart] using hz.symm
    apply Polynomial.ext
    intro n
    rw [hcoeff, hinput, evenPart_circleNumerator]
  have hodd : (oddC q).toPoly = fractionalLift 511 (initialP1 m) := by
    have hcoeff : ∀ n, (oddC q).toPoly.coeff n =
        (oddPart q.toPoly).coeff n := by
      intro n
      rw [oddC_coeff]
      by_cases hn : n < 512
      · simp only [if_pos hn]
        exact (monomialPolynomial_coeff
          (fun i : Fin 512 => (2 : K)⁻¹ * q.toPoly.coeff (2 * i.val + 1))
            ⟨n, hn⟩).symm
      · simp only [if_neg hn]
        have hz := monomialPolynomial_coeff_eq_zero_of_ge
          (fun i : Fin 512 => (2 : K)⁻¹ * q.toPoly.coeff (2 * i.val + 1)) n (by omega)
        simpa [oddPart] using hz.symm
    apply Polynomial.ext
    intro n
    rw [hcoeff, hinput, oddPart_circleNumerator]
  have hdec0 : (decodeFractionalLiftC 512 nodes0 (evenC q)).toPoly =
      initialP0 m := by
    have hbridge : (decodeFractionalLiftC 512 nodes0 (evenC q)).toPoly =
        AspisWide.InitialInverse.decodeFractionalLift 512 nodes0 havoid0
          (evenC q).toPoly := by
      exact AspisWide.InitialInverseBridge.decodeFractionalLiftC_toPoly_eq
        512 nodes0 havoid0 (evenC q)
    rw [hbridge, heven]
    exact decodeFractionalLift_fractionalLift 512 nodes0 hinj0 havoid0
      (initialP0 m) (by have hh := initialP0_degree_lt m; omega)
  have hdec1 : (decodeFractionalLiftC 511 nodes1 (oddC q)).toPoly =
      initialP1 m := by
    have hbridge : (decodeFractionalLiftC 511 nodes1 (oddC q)).toPoly =
        AspisWide.InitialInverse.decodeFractionalLift 511 nodes1 havoid1
          (oddC q).toPoly := by
      exact AspisWide.InitialInverseBridge.decodeFractionalLiftC_toPoly_eq
        511 nodes1 havoid1 (oddC q)
    rw [hbridge, hodd]
    exact decodeFractionalLift_fractionalLift 511 nodes1 hinj1 havoid1
      (initialP1 m) (by have hh := initialP1_degree_lt m; omega)
  have henc0 : (encode (K := K) 511 (evenV m)).toPoly = initialP0 m := by
    rw [naturalPolynomial_encode, evenV_initial]
  have henc1 : (encode (K := K) 511 (oddV m)).toPoly = initialP1 m := by
    rw [naturalPolynomial_encode, oddV_initial]
  have hout0 : decodeFractionalLiftC 512 nodes0 (evenC q) =
      encode (K := K) 511 (evenV m) :=
    CompPoly.CPolynomial.toPolyLinearEquiv.injective <| by
      simpa only [CompPoly.CPolynomial.toPolyLinearEquiv_apply] using hdec0.trans henc0.symm
  have hout1 : decodeFractionalLiftC 511 nodes1 (oddC q) =
      encode (K := K) 511 (oddV m) :=
    CompPoly.CPolynomial.toPolyLinearEquiv.injective <| by
      simpa only [CompPoly.CPolynomial.toPolyLinearEquiv_apply] using hdec1.trans henc1.symm
  exact AspisWide.InitialMessageComputableV4.decodeMessage_of_laneEncodings
    nodes0 nodes1 q m hout0 hout1

#print axioms decodeMessage_of_circleNumerator
end AspisWide.InitialMessageComputableV5
