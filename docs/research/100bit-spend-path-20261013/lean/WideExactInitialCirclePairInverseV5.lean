import WideExactInitialInverseV5
import AspisFormal.V5FriConcreteEncoderApplicability

set_option autoImplicit false
namespace AspisWide.InitialCirclePairInverse
open Polynomial
open AspisWide.InitialInverse
open AspisV5FriCircleEncoderDistance
open AspisV5FriConcreteEncoderApplicability

noncomputable section
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K] [NeZero (2 : K)]

/-- Read even coefficients of an ambient numerator. -/
def evenPart (f : K[X]) : K[X] :=
  monomialPolynomial (fun i : Fin 513 => f.coeff (2 * i.val))

/-- Read odd coefficients and undo the released factor of two. -/
def oddPart (f : K[X]) : K[X] :=
  monomialPolynomial (fun i : Fin 512 => (2 : K)⁻¹ * f.coeff (2 * i.val + 1))

theorem evenPart_circleNumerator (p0 p1 : K[X]) :
    evenPart (circleNumerator p0 p1) = fractionalLift 512 p0 := by
  ext n
  have hnum : circleNumerator p0 p1 =
      Polynomial.expand K 2 (fractionalLift 512 p0) +
        (Polynomial.C 2 * X) * Polynomial.expand K 2 (fractionalLift 511 p1) := by
    rw [circleNumerator, mobiusLift_eq_expand, mobiusLift_eq_expand]
  by_cases hn : n < 513
  · have hm := monomialPolynomial_coeff
      (fun i : Fin 513 => (circleNumerator p0 p1).coeff (2 * i.val))
      ⟨n, hn⟩
    calc
      (monomialPolynomial (fun i : Fin 513 =>
        (circleNumerator p0 p1).coeff (2 * i.val))).coeff n =
          (circleNumerator p0 p1).coeff (2 * n) := by
            simpa only [Fin.val_mk] using hm
      _ = (fractionalLift 512 p0).coeff n := by
        rw [hnum, Polynomial.coeff_add, coeff_expand_two_even,
          coeff_scaledX_expand_two_even, add_zero]
  · have hnge : 513 ≤ n := by omega
    have hleft : (evenPart (circleNumerator p0 p1)).coeff n = 0 := by
      simpa only [evenPart] using
        (monomialPolynomial_coeff_eq_zero_of_ge
          (fun i : Fin 513 => (circleNumerator p0 p1).coeff (2 * i.val)) n hnge)
    rw [hleft]
    have hdeg : (fractionalLift 512 p0).natDegree ≤ 512 :=
      fractionalLift_natDegree_le 512 p0
    have hnlt : (fractionalLift 512 p0).natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hnlt]

theorem oddPart_circleNumerator (p0 p1 : K[X]) :
    oddPart (circleNumerator p0 p1) = fractionalLift 511 p1 := by
  ext n
  have hnum : circleNumerator p0 p1 =
      Polynomial.expand K 2 (fractionalLift 512 p0) +
        (Polynomial.C 2 * X) * Polynomial.expand K 2 (fractionalLift 511 p1) := by
    rw [circleNumerator, mobiusLift_eq_expand, mobiusLift_eq_expand]
  by_cases hn : n < 512
  · have hm := monomialPolynomial_coeff
      (fun i : Fin 512 => (2 : K)⁻¹ *
        (circleNumerator p0 p1).coeff (2 * i.val + 1))
      ⟨n, hn⟩
    calc
      (monomialPolynomial (fun i : Fin 512 => (2 : K)⁻¹ *
        (circleNumerator p0 p1).coeff (2 * i.val + 1))).coeff n =
          (2 : K)⁻¹ * (circleNumerator p0 p1).coeff (2 * n + 1) := by
            simpa only [Fin.val_mk] using hm
      _ = (fractionalLift 511 p1).coeff n := by
        rw [hnum, Polynomial.coeff_add, coeff_expand_two_odd,
          coeff_scaledX_expand_two_odd, zero_add]
        field_simp
  · have hnge : 512 ≤ n := by omega
    have hleft : (oddPart (circleNumerator p0 p1)).coeff n = 0 := by
      simpa only [oddPart] using
        (monomialPolynomial_coeff_eq_zero_of_ge
          (fun i : Fin 512 => (2 : K)⁻¹ *
            (circleNumerator p0 p1).coeff (2 * i.val + 1)) n hnge)
    rw [hleft]
    have hdeg : (fractionalLift 511 p1).natDegree ≤ 511 :=
      fractionalLift_natDegree_le 511 p1
    have hnlt : (fractionalLift 511 p1).natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hnlt]

theorem decodeCircleNumerator_pair
    (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (hinj0 : Function.Injective nodes0) (hinj1 : Function.Injective nodes1)
    (havoid0 : ∀ i, nodes0 i ≠ -1) (havoid1 : ∀ i, nodes1 i ≠ -1)
    (p0 p1 : K[X]) (hp0 : p0.natDegree ≤ 512)
    (hp1 : p1.natDegree ≤ 511) :
    (decodeFractionalLift 512 nodes0 havoid0 (evenPart (circleNumerator p0 p1)),
      decodeFractionalLift 511 nodes1 havoid1 (oddPart (circleNumerator p0 p1))) =
      (p0, p1) := by
  rw [evenPart_circleNumerator, oddPart_circleNumerator]
  exact Prod.ext
    (decodeFractionalLift_fractionalLift 512 nodes0 hinj0 havoid0 p0 hp0)
    (decodeFractionalLift_fractionalLift 511 nodes1 hinj1 havoid1 p1 hp1)

#print axioms decodeCircleNumerator_pair
end
end AspisWide.InitialCirclePairInverse
