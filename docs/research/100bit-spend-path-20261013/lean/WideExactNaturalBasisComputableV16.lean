import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Nat.BitIndices

/-!
An executable CPolynomial realization of the Chebyshev factors used by the
natural line basis.  The conversion to Mathlib polynomials is proof-only.
-/

open Polynomial Polynomial.Chebyshev

namespace AspisWide.NaturalBasisComputable

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

/-- Computable recurrence for `T_(2^b)`, using only CPolynomial operations. -/
def cChebPow : Nat → CompPoly.CPolynomial K
  | 0 => CompPoly.CPolynomial.X
  | b + 1 =>
      (CompPoly.CPolynomial.C (2 : K) * cChebPow b) * cChebPow b -
        CompPoly.CPolynomial.C (1 : K)

theorem cChebPow_toPoly : ∀ b,
    (cChebPow (K := K) b).toPoly = T K (2 ^ b : ℕ)
  | 0 => by
      change (CompPoly.CPolynomial.X : CompPoly.CPolynomial K).toPoly = T K 1
      rw [CompPoly.CPolynomial.X_toPoly]
      simp
  | b + 1 => by
      rw [cChebPow, CompPoly.CPolynomial.toPoly_sub,
        CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.toPoly_mul,
        cChebPow_toPoly b]
      have hconst (x : K) :
          (CompPoly.CPolynomial.C x : CompPoly.CPolynomial K).toPoly = C x := by
        exact CompPoly.CPolynomial.C_toPoly x
      rw [hconst 2, hconst 1]
      rw [show (2 ^ (b + 1) : ℕ) = 2 * 2 ^ b by omega]
      push_cast
      rw [T_mul, T_two]
      rw [Polynomial.sub_comp, Polynomial.mul_X_pow_comp,
        Polynomial.ofNat_comp, Polynomial.one_comp]
      rw [← Polynomial.C_eq_natCast (R := K) 2]
      simp only [Polynomial.C_1, Nat.cast_ofNat]
      ring

/-- Executable product of the power-of-two Chebyshev factors selected by the
binary expansion of an index. -/
def cNaturalLinePoly (index : Nat) : CompPoly.CPolynomial K :=
  index.bitIndices.foldr (fun bit acc => cChebPow (K := K) bit * acc) 1

private theorem cChebProduct_toPoly (bits : List Nat) :
    ((bits.foldr (fun bit acc => cChebPow (K := K) bit * acc) 1).toPoly) =
      (bits.map fun bit => T K (2 ^ bit : ℕ)).prod := by
  induction bits with
  | nil => simp only [List.foldr, CompPoly.CPolynomial.toPoly_one, List.map,
    List.prod_nil]
  | cons bit rest ih =>
      simp only [List.foldr]
      rw [CompPoly.CPolynomial.toPoly_mul, cChebPow_toPoly, ih]
      simp

/-- The executable factor product is exactly the natural-line basis in
Mathlib's polynomial representation. -/
theorem cNaturalLinePoly_toPoly (index : Nat) :
    (cNaturalLinePoly (K := K) index).toPoly =
      ∏ bit ∈ index.bitIndices.toFinset, T K (2 ^ bit : ℕ) := by
  rw [cNaturalLinePoly, cChebProduct_toPoly]
  exact (List.prod_toFinset _ Nat.bitIndices_nodup).symm

end AspisWide.NaturalBasisComputable
