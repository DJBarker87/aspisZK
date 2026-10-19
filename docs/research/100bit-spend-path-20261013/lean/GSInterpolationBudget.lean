import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace AspisWide.GSInterpolationBudget

def weightedCount (d D ell : Nat) : Nat :=
  (Finset.range (ell + 1)).sum fun j => D - d * j + 1

theorem weightedCount_eq_closedForm (d D ell : Nat) (htri : d * ell ≤ D) :
    weightedCount d D ell = (ell + 1) * (D + 1) - d * ((ell + 1) * ell / 2) := by
  classical
  unfold weightedCount
  have hterm (j : Nat) (hj : j ∈ Finset.range (ell + 1)) :
      D - d * j + 1 = (D + 1) - d * j := by
    have hjle : j ≤ ell := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hmul : d * j ≤ D := Nat.le_trans (Nat.mul_le_mul_left d hjle) htri
    omega
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    rw [Finset.sum_range_id]
    simp [Nat.add_sub_cancel]
  · intro j hj
    have hjle : j ≤ ell := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (Nat.le_trans (Nat.mul_le_mul_left d hjle) htri).trans (Nat.le_succ D)

 theorem initial_weighted_count : weightedCount 1024 114689 112 = 6480098 := by
  rw [weightedCount_eq_closedForm 1024 114689 112 (by norm_num)]

theorem final_weighted_count : weightedCount 255 28673 112 = 1626522 := by
  rw [weightedCount_eq_closedForm 255 28673 112 (by norm_num)]

#print axioms weightedCount_eq_closedForm
#print axioms initial_weighted_count
#print axioms final_weighted_count

end AspisWide.GSInterpolationBudget
