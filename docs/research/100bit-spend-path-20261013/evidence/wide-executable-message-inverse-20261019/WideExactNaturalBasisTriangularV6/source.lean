import WideExactNaturalBasisTriangularV4
import AspisFormal.CircleNaturalBasisEval

/-! The executable CPolynomial basis agrees with the lightweight evaluator
basis definition, without importing the unrelated matrix corpus. -/
namespace AspisWide.NaturalBasisTriangularV4

open AspisWide.NaturalBasisComputable

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

theorem basis_toPoly (i : Nat) :
    (basis (K := K) i).toPoly = AspisCircleTensorBinding.naturalLinePoly K i := by
  rw [basis, cNaturalLinePoly_toPoly,
    AspisCircleTensorBinding.naturalLinePoly]

#print axioms basis_toPoly

end AspisWide.NaturalBasisTriangularV4
