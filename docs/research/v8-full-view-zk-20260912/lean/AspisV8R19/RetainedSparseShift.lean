/- Retained symbolic proof from V5GoodGateSparseShift.lean
SHA256 27e474d523dd443e02027e2c77a6c63c978989ef86a4717d3328af58433b35fa. See extract_r45_sparse_shift.py. -/
import AspisV8R16.NaturalBasisCore
import Mathlib.Tactic.Ring
namespace AspisR19.RetainedSparseShift
open Matrix Polynomial Polynomial.Chebyshev AspisCircleTensorBinding
variable {K : Type*} [Field K] [NeZero (2 : K)]
/-- Number of consecutive low one-bits.  This is the mathematical graph of
Rust's `usize::trailing_ones()` on the reachable indices `0..46`. -/
def trailingOnes : Nat → Nat
  | n => if n % 2 = 0 then 0 else 1 + trailingOnes (n / 2)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-- The coefficient obtained after `count` calls to `M31::half()`. -/
def dyadic (count : Nat) : K := ((2 : K) ^ count)⁻¹

omit [NeZero (2 : K)] in
@[simp] theorem dyadic_zero : dyadic (K := K) 0 = 1 := by
  simp [dyadic]

omit [NeZero (2 : K)] in
@[simp] theorem dyadic_succ (count : Nat) :
    dyadic (K := K) (count + 1) =
      (2 : K)⁻¹ * dyadic (K := K) count := by
  simp [dyadic, pow_succ, _root_.mul_inv_rev, mul_comm]

omit [NeZero (2 : K)] in
theorem naturalLinePoly_even (index : Nat) :
    naturalLinePoly K (2 * index) =
      (naturalLinePoly K index).comp (T K 2) := by
  simp only [naturalLinePoly, Nat.bitIndices_two_mul]
  rw [Polynomial.prod_comp]
  rw [show (index.bitIndices.map (fun bit => bit + 1)).toFinset =
      index.bitIndices.toFinset.image (fun bit => bit + 1) by
        ext bit
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro bit hbit
    simpa [pow_succ, mul_comm] using (T_mul K (2 ^ bit : ℤ) 2)
  · intro left _ right _ equal
    exact Nat.add_right_cancel equal

omit [NeZero (2 : K)] in
theorem naturalLinePoly_odd (index : Nat) :
    naturalLinePoly K (2 * index + 1) =
      X * naturalLinePoly K (2 * index) := by
  rw [naturalLinePoly, Nat.bitIndices_two_mul_add_one,
    List.toFinset_cons, Finset.prod_insert]
  · rw [naturalLinePoly, Nat.bitIndices_two_mul]
    simp
  · simp

omit [NeZero (2 : K)] in
@[simp] theorem naturalLinePoly_comp_T_two (index : Nat) :
    (naturalLinePoly K index).comp (T K 2) =
      naturalLinePoly K (2 * index) :=
  (naturalLinePoly_even index).symm

/-- A recurrence with the exact same even/odd branches as Rust, but phrased
as polynomials so its correctness can be proved once by strong induction. -/
noncomputable def recursiveShiftPolynomial (index : Nat) : K[X] :=
  if hEven : index % 2 = 0 then
    naturalLinePoly K (index + 1)
  else
    C ((2 : K)⁻¹) * naturalLinePoly K (index - 1) +
      C ((2 : K)⁻¹) *
        (recursiveShiftPolynomial (index / 2)).comp (T K 2)
termination_by index
decreasing_by
  have hpositive : 0 < index := by
    by_contra hzero
    have : index = 0 := by omega
    subst index
    simp at hEven
  exact Nat.div_lt_self hpositive (by omega)

theorem recursiveShiftPolynomial_eq_mul_X (index : Nat) :
    recursiveShiftPolynomial (K := K) index =
      X * naturalLinePoly K index := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [recursiveShiftPolynomial]
      split
      case isTrue hEven =>
        have heven : Even index := Nat.even_iff.mpr hEven
        obtain ⟨halfIndex, rfl⟩ := even_iff_exists_two_mul.mp heven
        rw [naturalLinePoly_odd]
      case isFalse hOdd =>
        have hmod : index % 2 = 1 := by omega
        have hodd : Odd index := Nat.odd_iff.mpr hmod
        obtain ⟨halfIndex, rfl⟩ := Odd.exists_bit1 hodd
        have hdiv : (2 * halfIndex + 1) / 2 = halfIndex := by omega
        simp only [Nat.add_sub_cancel]
        rw [hdiv, ih halfIndex (by omega), mul_comp, X_comp,
          naturalLinePoly_odd, naturalLinePoly_even]
        rw [T_two]
        have hhalf : C ((2 : K)⁻¹) * (2 : K[X]) = 1 := by
          rw [← C_ofNat, ← Polynomial.C_mul,
            inv_mul_cancel₀ (NeZero.ne 2)]
          exact map_one (Polynomial.C : K →+* K[X])
        calc
          C ((2 : K)⁻¹) *
                (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1) +
              C ((2 : K)⁻¹) *
                ((2 * X ^ 2 - 1) *
                  (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1)) =
              (C ((2 : K)⁻¹) * (2 : K[X])) *
                (X ^ 2 *
                  (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1)) := by
            ring
          _ = X ^ 2 *
                (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1) := by
            rw [hhalf, one_mul]
          _ = X *
                (X * (naturalLinePoly K halfIndex).comp (2 * X ^ 2 - 1)) := by
            simp only [pow_two, mul_assoc]

theorem trailingOnes_of_even (index : Nat) (hEven : index % 2 = 0) :
    trailingOnes index = 0 := by
  rw [trailingOnes, if_pos hEven]

theorem trailingOnes_of_odd (index : Nat) (hOdd : index % 2 ≠ 0) :
    trailingOnes index = 1 + trailingOnes (index / 2) := by
  rw [trailingOnes, if_neg hOdd]

@[simp] theorem trailingOnes_two_mul_add_one (index : Nat) :
    trailingOnes (2 * index + 1) = 1 + trailingOnes index := by
  rw [trailingOnes]
  have hmod : (2 * index + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  congr 1
  congr 1
  omega

theorem pow_trailingOnes_le_succ (index : Nat) :
    2 ^ trailingOnes index ≤ index + 1 := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      by_cases hEven : index % 2 = 0
      · rw [trailingOnes_of_even index hEven]
        simp
      · rw [trailingOnes_of_odd index hEven, pow_add, pow_one]
        have hpositive : 0 < index := by
          by_contra hzero
          have : index = 0 := by omega
          subst index
          simp at hEven
        have hhalf : index / 2 < index := Nat.div_lt_self hpositive (by omega)
        have hrec := ih (index / 2) hhalf
        have hmod : index % 2 = 1 := by omega
        omega

/-- Nat-indexed spelling of one sparse column; using `Finset.range` matches
the Rust `0..count` carry loop without dependent casts. -/
noncomputable def sparseFormula (index : Nat) : K[X] :=
  if index % 2 = 0 then
    naturalLinePoly K (index + 1)
  else
    let count := trailingOnes index
    C (dyadic count) * naturalLinePoly K (index + 1) +
      ∑ carry ∈ Finset.range count,
        C (dyadic (carry + 1)) *
          naturalLinePoly K (index - (2 ^ (carry + 1) - 1))

omit [NeZero (2 : K)] in
theorem sparseFormula_eq_carry_expansion (index : Nat) :
    sparseFormula (K := K) index =
      C (dyadic (K := K) (trailingOnes index)) *
          naturalLinePoly K (index + 1) +
        ∑ carry ∈ Finset.range (trailingOnes index),
          C (dyadic (K := K) (carry + 1)) *
            naturalLinePoly K (index - (2 ^ (carry + 1) - 1)) := by
  rw [sparseFormula]
  by_cases hEven : index % 2 = 0
  · rw [if_pos hEven, trailingOnes_of_even index hEven]
    simp
  · rw [if_neg hEven]

theorem carry_index_double (index carry : Nat)
    (hcarry : carry < trailingOnes index) :
    2 * index + 1 - (2 ^ (carry + 2) - 1) =
      2 * (index - (2 ^ (carry + 1) - 1)) := by
  have hpow : 2 ^ (carry + 1) ≤ 2 ^ trailingOnes index := by
    exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt hcarry)
  have htop := pow_trailingOnes_le_succ index
  have hbound : 2 ^ (carry + 1) - 1 ≤ index := by omega
  have hcancel := Nat.sub_add_cancel hbound
  have hpositive : 0 < 2 ^ (carry + 1) := pow_pos (by omega) _
  have hdouble :
      2 ^ (carry + 2) - 1 =
        2 * (2 ^ (carry + 1) - 1) + 1 := by
    rw [show carry + 2 = (carry + 1) + 1 by omega, pow_succ]
    omega
  rw [hdouble]
  omega

omit [NeZero (2 : K)] in
theorem sparseFormula_odd_recurrence (index : Nat) :
    sparseFormula (K := K) (2 * index + 1) =
      C ((2 : K)⁻¹) * naturalLinePoly K (2 * index) +
        C ((2 : K)⁻¹) *
          (sparseFormula (K := K) index).comp (T K 2) := by
  rw [sparseFormula_eq_carry_expansion, sparseFormula_eq_carry_expansion]
  rw [trailingOnes_two_mul_add_one]
  simp only [Nat.one_add, Finset.sum_range_succ']
  have hmain :
      C (dyadic (K := K) (trailingOnes index).succ) *
          naturalLinePoly K (2 * index + 1 + 1) =
        C ((2 : K)⁻¹) *
          (C (dyadic (K := K) (trailingOnes index)) *
            naturalLinePoly K (index + 1)).comp (T K 2) := by
    rw [show (trailingOnes index).succ = trailingOnes index + 1 by omega,
      dyadic_succ, map_mul, mul_comp, C_comp]
    rw [show 2 * index + 1 + 1 = 2 * (index + 1) by omega,
      naturalLinePoly_even]
    ring
  have hfirst :
      C (dyadic (K := K) (0 + 1)) *
          naturalLinePoly K (2 * index + 1 - (2 ^ (0 + 1) - 1)) =
        C ((2 : K)⁻¹) * naturalLinePoly K (2 * index) := by
    simp [dyadic]
  have htail :
      (∑ carry ∈ Finset.range (trailingOnes index),
        C (dyadic (K := K) (carry + 1 + 1)) *
          naturalLinePoly K
            (2 * index + 1 - (2 ^ (carry + 1 + 1) - 1))) =
        C ((2 : K)⁻¹) *
          (∑ carry ∈ Finset.range (trailingOnes index),
            C (dyadic (K := K) (carry + 1)) *
              naturalLinePoly K
                (index - (2 ^ (carry + 1) - 1))).comp (T K 2) := by
    rw [Polynomial.sum_comp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro carry hcarry
    have hcarry' := Finset.mem_range.mp hcarry
    rw [mul_comp, C_comp, naturalLinePoly_comp_T_two]
    rw [show carry + 1 + 1 = (carry + 1) + 1 by omega,
      dyadic_succ, map_mul]
    rw [carry_index_double index carry hcarry']
    ring
  rw [hmain, hfirst, htail, add_comp]
  ring

omit [NeZero (2 : K)] in
theorem sparseFormula_eq_recursive (index : Nat) :
    sparseFormula (K := K) index =
      recursiveShiftPolynomial (K := K) index := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      rw [recursiveShiftPolynomial]
      by_cases hEven : index % 2 = 0
      · rw [dif_pos hEven, sparseFormula, if_pos hEven]
      · rw [dif_neg hEven]
        have hpositive : 0 < index := by
          by_contra hzero
          have : index = 0 := by omega
          subst index
          simp at hEven
        have hhalf : index / 2 < index := Nat.div_lt_self hpositive (by omega)
        have hmod : index % 2 = 1 := by omega
        have hshape : index = 2 * (index / 2) + 1 := by omega
        have hsub : index - 1 = 2 * (index / 2) := by omega
        conv_lhs => rw [hshape, sparseFormula_odd_recurrence]
        rw [ih (index / 2) hhalf, hsub]


#print axioms dyadic_zero
#print axioms dyadic_succ
#print axioms naturalLinePoly_even
#print axioms naturalLinePoly_odd
#print axioms naturalLinePoly_comp_T_two
#print axioms recursiveShiftPolynomial_eq_mul_X
#print axioms trailingOnes_of_even
#print axioms trailingOnes_of_odd
#print axioms trailingOnes_two_mul_add_one
#print axioms pow_trailingOnes_le_succ
#print axioms sparseFormula_eq_carry_expansion
#print axioms carry_index_double
#print axioms sparseFormula_odd_recurrence
#print axioms sparseFormula_eq_recursive
end AspisR19.RetainedSparseShift
