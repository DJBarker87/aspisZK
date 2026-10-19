import WideExactNaturalBasisTriangularV8
import CompPoly.Univariate.ToPoly.Impl

/-! The executable encoder is degree-bounded, enabling top-down cancellation. -/
namespace AspisWide.NaturalBasisTriangularV4

open AspisWide.NaturalBasisComputable

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

theorem encode_degree (n : Nat) (c : Fin (n + 1) → K) :
    (encode (K := K) n c).toPoly.natDegree ≤ n := by
  induction n with
  | zero =>
      rw [encode, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly, basis_toPoly]
      simpa [naturalLinePoly_natDegree_local]
        using (Polynomial.natDegree_C_mul_le (c 0)
          (AspisCircleTensorBinding.naturalLinePoly K 0))
  | succ n ih =>
      rw [encode, CompPoly.CPolynomial.toPoly_add,
        CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly,
        basis_toPoly]
      have hlower := ih (fun i => c i.castSucc)
      have htop := Polynomial.natDegree_C_mul_le
        (c (Fin.last (n + 1)))
        (AspisCircleTensorBinding.naturalLinePoly K (n + 1))
      rw [naturalLinePoly_natDegree_local] at htop
      exact (Polynomial.natDegree_add_le _ _).trans (by omega)

#print axioms encode_degree

end AspisWide.NaturalBasisTriangularV4
