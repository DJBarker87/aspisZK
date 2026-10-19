import WideExactNaturalBasisTriangularV6
import Mathlib.RingTheory.Polynomial.Chebyshev

/-! Small degree/diagonal facts for the natural basis, proved from the
lightweight definition rather than importing the matrix corpus. -/
namespace AspisWide.NaturalBasisTriangularV4

open Polynomial Polynomial.Chebyshev

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

theorem naturalLinePoly_ne_zero_local (i : Nat) :
    AspisCircleTensorBinding.naturalLinePoly K i ≠ 0 := by
  rw [AspisCircleTensorBinding.naturalLinePoly]
  apply Finset.prod_ne_zero_iff.mpr
  intro bit hbit
  exact T_ne_zero K (2 ^ bit : ℕ)

theorem naturalLinePoly_natDegree_local (i : Nat) :
    (AspisCircleTensorBinding.naturalLinePoly K i).natDegree = i := by
  rw [AspisCircleTensorBinding.naturalLinePoly, Polynomial.natDegree_prod]
  · simp [List.sum_toFinset _ Nat.bitIndices_nodup]
  · intro bit hbit
    exact T_ne_zero K (2 ^ bit : ℕ)

theorem basis_degree (i : Nat) : (basis (K := K) i).toPoly.natDegree = i := by
  rw [basis_toPoly]
  exact naturalLinePoly_natDegree_local i

theorem basis_diagonal_ne_zero (i : Nat) :
    (basis (K := K) i).toPoly.coeff i ≠ 0 := by
  rw [basis_toPoly]
  have hpoly := naturalLinePoly_ne_zero_local (K := K) i
  have hlead : (AspisCircleTensorBinding.naturalLinePoly K i).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hpoly
  simpa [Polynomial.leadingCoeff, naturalLinePoly_natDegree_local] using hlead

#print axioms naturalLinePoly_ne_zero_local
#print axioms naturalLinePoly_natDegree_local
#print axioms basis_degree
#print axioms basis_diagonal_ne_zero

end AspisWide.NaturalBasisTriangularV4
