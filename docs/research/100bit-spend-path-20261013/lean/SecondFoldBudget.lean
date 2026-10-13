import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Numeric feasibility checks for a proposed second-fold parameter set.

These results certify only the stated arithmetic. They do not establish the
existence of a second-fold decoder or justify a correlated-agreement security
cap. `agreementThreshold` is the minimum agreement count 2390. A later
`ValidResponse` interface whose parameter is a strict threshold would use
2389 to express agreement count at least 2390. -/

set_option autoImplicit false

namespace AspisR1.SecondFoldBudget

def n : Nat := 65536
def messageDegree : Nat := 63
def multiplicity : Nat := 3
def agreementThreshold : Nat := 2390
def weightedDegree : Nat := 7169
def xBound : Nat := 7170
def ell : Nat := 112
def yRows : Nat := 113
def curveDegree : Nat := 3
def zBound : Nat := 2533

theorem xBound_eq : xBound = weightedDegree + 1 := by decide

theorem yRows_eq : yRows = ell + 1 := by decide

theorem message_degree_product_le_weighted_degree :
    messageDegree * ell ≤ weightedDegree := by
  norm_num [messageDegree, ell, weightedDegree]

/-- The threshold here is a minimum count, not the strict-count parameter. -/
theorem weighted_degree_lt_multiplicity_times_minimum_agreement :
    weightedDegree < multiplicity * agreementThreshold := by
  norm_num [weightedDegree, multiplicity, agreementThreshold]

theorem y_degree_lt_row_count : ell < yRows := by
  norm_num [ell, yRows]

private theorem sum_range_sq_mul_six (m : Nat) :
    (∑ j ∈ Finset.range m, j ^ 2) * 6 = m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ]
      cases m with
      | zero => norm_num
      | succ k =>
          have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          have h2 : 2 * (k + 1 + 1) - 1 = 2 * k + 3 := by omega
          have h3 : k + 1 + 1 - 1 = k + 1 := by omega
          rw [Nat.succ_sub_one, h1] at ih
          rw [h2, h3]
          nlinarith [ih]

/-- Exact finite sum of the supplied weighted-degree term for indices 0 through
112, obtained from the closed forms for the first and second power sums. -/
theorem exact_weighted_sum :
    (∑ j ∈ Finset.range yRows,
      (xBound - messageDegree * j) * (zBound - curveDegree * j)) = 996030138 := by
  rw [← Finset.sum_range_reflect
    (fun j => (xBound - messageDegree * j) * (zBound - curveDegree * j)) yRows]
  have hterm (j : Nat) (hj : j ∈ Finset.range yRows) :
      (xBound - messageDegree * (yRows - 1 - j)) *
          (zBound - curveDegree * (yRows - 1 - j)) =
        (114 + 63 * j) * (2197 + 3 * j) := by
    have hj' : j < 113 := by simpa [yRows] using hj
    have hfirst :
        xBound - messageDegree * (yRows - 1 - j) = 114 + 63 * j := by
      norm_num [xBound, messageDegree, yRows]
      omega
    have hsecond :
        zBound - curveDegree * (yRows - 1 - j) = 2197 + 3 * j := by
      norm_num [zBound, curveDegree, yRows]
      omega
    rw [hfirst, hsecond]
  calc
    (∑ j ∈ Finset.range yRows,
        (xBound - messageDegree * (yRows - 1 - j)) *
          (zBound - curveDegree * (yRows - 1 - j))) =
        ∑ j ∈ Finset.range yRows, (114 + 63 * j) * (2197 + 3 * j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j hj
    _ = 996030138 := by
      have hy : yRows = 113 := by norm_num [yRows]
      have hpoly (j : Nat) :
          (114 + 63 * j) * (2197 + 3 * j) =
            114 * 2197 + (114 * 3 + 63 * 2197) * j + (63 * 3) * j ^ 2 := by
        ring
      have hsum :
          (∑ j ∈ Finset.range yRows, (114 + 63 * j) * (2197 + 3 * j)) =
            yRows * (114 * 2197) +
              (114 * 3 + 63 * 2197) * (∑ j ∈ Finset.range yRows, j) +
              (63 * 3) * (∑ j ∈ Finset.range yRows, j ^ 2) := by
        calc
          _ = ∑ j ∈ Finset.range yRows,
                (114 * 2197 + (114 * 3 + 63 * 2197) * j +
                  (63 * 3) * j ^ 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hpoly j
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
              rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
              rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsum]
      rw [Finset.sum_range_id]
      have hsquare : (∑ j ∈ Finset.range yRows, j ^ 2) = 474600 := by
        have h := sum_range_sq_mul_six yRows
        rw [hy] at h
        norm_num [yRows] at h
        rw [hy]
        omega
      rw [hsquare]
      norm_num [yRows]

theorem exact_constraint_count : 6 * n * zBound = 996016128 := by
  norm_num [n, zBound]

theorem exact_surplus :
    996030138 - 6 * n * zBound = 14010 := by
  norm_num [n, zBound]

theorem weighted_sum_exceeds_constraint_count :
    6 * n * zBound <
      (∑ j ∈ Finset.range yRows,
        (xBound - messageDegree * j) * (zBound - curveDegree * j)) := by
  rw [exact_weighted_sum, exact_constraint_count]
  norm_num

/-- Exact branch-route expression supplied for this proposed parameter set. -/
theorem exact_branch_route_expression :
    zBound + 224 * yRows * zBound +
      58 * 64 * yRows ^ 2 * zBound + (3 * n + 1) * yRows = 120146806070 := by
  norm_num [zBound, yRows, n]

theorem branch_route_expression_lt_two_pow_37 :
    zBound + 224 * yRows * zBound +
      58 * 64 * yRows ^ 2 * zBound + (3 * n + 1) * yRows < 2 ^ 37 := by
  rw [exact_branch_route_expression]
  norm_num

theorem numeric_feasibility_certificate :
    messageDegree * ell ≤ weightedDegree ∧
    weightedDegree < multiplicity * agreementThreshold ∧
    ell < yRows ∧
    6 * n * zBound <
      (∑ j ∈ Finset.range yRows,
        (xBound - messageDegree * j) * (zBound - curveDegree * j)) ∧
    zBound + 224 * yRows * zBound +
      58 * 64 * yRows ^ 2 * zBound + (3 * n + 1) * yRows < 2 ^ 37 := by
  exact ⟨message_degree_product_le_weighted_degree,
    weighted_degree_lt_multiplicity_times_minimum_agreement,
    y_degree_lt_row_count,
    weighted_sum_exceeds_constraint_count,
    branch_route_expression_lt_two_pow_37⟩

#print axioms exact_weighted_sum
#print axioms numeric_feasibility_certificate

end AspisR1.SecondFoldBudget
