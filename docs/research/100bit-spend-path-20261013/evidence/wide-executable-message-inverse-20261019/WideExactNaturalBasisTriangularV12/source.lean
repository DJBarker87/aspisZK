import WideExactNaturalBasisTriangularV9
import CompPoly.Univariate.ToPoly.Impl

/-! The encoder's top coefficient exposes the last natural-basis coordinate. -/
namespace AspisWide.NaturalBasisTriangularV4

open AspisWide.NaturalBasisComputable

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

theorem encode_top_coeff (n : Nat) (c : Fin (n + 2) → K) :
    (encode (K := K) (n + 1) c).toPoly.coeff (n + 1) =
      c (Fin.last (n + 1)) * (basis (K := K) (n + 1)).toPoly.coeff (n + 1) := by
  rw [encode, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly,
    basis_toPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  have hdeg := encode_degree (K := K) n (fun i => c i.castSucc)
  have hlow : (encode (K := K) n (fun i => c i.castSucc)).toPoly.coeff (n + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hlow, zero_add]

theorem decode_encode_last (n : Nat) (c : Fin (n + 2) → K) :
    decode (K := K) (n + 1) (encode (K := K) (n + 1) c) (Fin.last (n + 1)) =
      c (Fin.last (n + 1)) := by
  simp only [decode, Fin.lastCases_last]
  rw [CompPoly.CPolynomial.coeff_toPoly, encode_top_coeff,
    CompPoly.CPolynomial.coeff_toPoly]
  exact mul_div_cancel_right₀ _ (basis_diagonal_ne_zero (K := K) (n + 1))

#print axioms encode_top_coeff
#print axioms decode_encode_last

end AspisWide.NaturalBasisTriangularV4
