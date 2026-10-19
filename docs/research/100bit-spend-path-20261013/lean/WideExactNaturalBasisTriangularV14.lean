import WideExactNaturalBasisTriangularV12
import CompPoly.Univariate.ToPoly.Impl

/-! Full executable inverse on coefficient vectors: top-down cancellation makes
this decoder a left inverse of the recursive encoder in every width. -/
namespace AspisWide.NaturalBasisTriangularV4

open AspisWide.NaturalBasisComputable

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

theorem encode_base_coeff (c : Fin 1 → K) :
    (encode (K := K) 0 c).toPoly.coeff 0 =
      c 0 * (basis (K := K) 0).toPoly.coeff 0 := by
  rw [encode, CompPoly.CPolynomial.toPoly_mul,
    CompPoly.CPolynomial.C_toPoly, Polynomial.coeff_C_mul]

theorem decode_encode (n : Nat) (c : Fin (n + 1) → K) :
    decode (K := K) n (encode (K := K) n c) = c := by
  induction n with
  | zero =>
      funext i
      fin_cases i
      have hquot : (encode (K := K) 0 c).coeff 0 /
          (basis (K := K) 0).coeff 0 = c 0 := by
        rw [CompPoly.CPolynomial.coeff_toPoly, encode_base_coeff,
          CompPoly.CPolynomial.coeff_toPoly]
        exact mul_div_cancel_right₀ _ (basis_diagonal_ne_zero (K := K) 0)
      simpa [decode] using hquot
  | succ n ih =>
      let lower : Fin (n + 1) → K := fun i => c i.castSucc
      let top : K := c (Fin.last (n + 1))
      have hquot : (encode (K := K) (n + 1) c).coeff (n + 1) /
          (basis (K := K) (n + 1)).coeff (n + 1) = top := by
        rw [CompPoly.CPolynomial.coeff_toPoly, encode_top_coeff,
          CompPoly.CPolynomial.coeff_toPoly]
        exact mul_div_cancel_right₀ _ (basis_diagonal_ne_zero (K := K) (n + 1))
      have hres : encode (K := K) (n + 1) c -
          CompPoly.CPolynomial.C top * basis (K := K) (n + 1) =
          encode (K := K) n lower := by
        rw [encode]
        dsimp [top, lower]
        exact add_sub_cancel_right _ _
      funext i
      simp only [decode, hquot, hres]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [top]
      · simpa [lower] using congrFun (ih lower) j

#print axioms encode_base_coeff
#print axioms decode_encode

end AspisWide.NaturalBasisTriangularV4
