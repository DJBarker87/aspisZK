/- SCC 12, rows [12, 13, 14, 15]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC12Matrix
import Mathlib.Tactic

namespace R752SCC12Rows04
open R752SCC12Matrix

theorem cell_12_0 : (B_scc * A_scc) (12 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_1 : (B_scc * A_scc) (12 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_2 : (B_scc * A_scc) (12 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_3 : (B_scc * A_scc) (12 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_4 : (B_scc * A_scc) (12 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_5 : (B_scc * A_scc) (12 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_6 : (B_scc * A_scc) (12 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_7 : (B_scc * A_scc) (12 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_8 : (B_scc * A_scc) (12 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_9 : (B_scc * A_scc) (12 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_10 : (B_scc * A_scc) (12 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_11 : (B_scc * A_scc) (12 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_12 : (B_scc * A_scc) (12 : Fin 16) (12 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_13 : (B_scc * A_scc) (12 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_14 : (B_scc * A_scc) (12 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_12_15 : (B_scc * A_scc) (12 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_12 : ∀ j, (B_scc * A_scc) (12 : Fin 16) j = if (12 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_12_0
  · simpa using cell_12_1
  · simpa using cell_12_2
  · simpa using cell_12_3
  · simpa using cell_12_4
  · simpa using cell_12_5
  · simpa using cell_12_6
  · simpa using cell_12_7
  · simpa using cell_12_8
  · simpa using cell_12_9
  · simpa using cell_12_10
  · simpa using cell_12_11
  · simpa using cell_12_12
  · simpa using cell_12_13
  · simpa using cell_12_14
  · simpa using cell_12_15
#print axioms row_12

theorem cell_13_0 : (B_scc * A_scc) (13 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_1 : (B_scc * A_scc) (13 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_2 : (B_scc * A_scc) (13 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_3 : (B_scc * A_scc) (13 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_4 : (B_scc * A_scc) (13 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_5 : (B_scc * A_scc) (13 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_6 : (B_scc * A_scc) (13 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_7 : (B_scc * A_scc) (13 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_8 : (B_scc * A_scc) (13 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_9 : (B_scc * A_scc) (13 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_10 : (B_scc * A_scc) (13 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_11 : (B_scc * A_scc) (13 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_12 : (B_scc * A_scc) (13 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_13 : (B_scc * A_scc) (13 : Fin 16) (13 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_14 : (B_scc * A_scc) (13 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_13_15 : (B_scc * A_scc) (13 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_13 : ∀ j, (B_scc * A_scc) (13 : Fin 16) j = if (13 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_13_0
  · simpa using cell_13_1
  · simpa using cell_13_2
  · simpa using cell_13_3
  · simpa using cell_13_4
  · simpa using cell_13_5
  · simpa using cell_13_6
  · simpa using cell_13_7
  · simpa using cell_13_8
  · simpa using cell_13_9
  · simpa using cell_13_10
  · simpa using cell_13_11
  · simpa using cell_13_12
  · simpa using cell_13_13
  · simpa using cell_13_14
  · simpa using cell_13_15
#print axioms row_13

theorem cell_14_0 : (B_scc * A_scc) (14 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_1 : (B_scc * A_scc) (14 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_2 : (B_scc * A_scc) (14 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_3 : (B_scc * A_scc) (14 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_4 : (B_scc * A_scc) (14 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_5 : (B_scc * A_scc) (14 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_6 : (B_scc * A_scc) (14 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_7 : (B_scc * A_scc) (14 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_8 : (B_scc * A_scc) (14 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_9 : (B_scc * A_scc) (14 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_10 : (B_scc * A_scc) (14 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_11 : (B_scc * A_scc) (14 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_12 : (B_scc * A_scc) (14 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_13 : (B_scc * A_scc) (14 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_14 : (B_scc * A_scc) (14 : Fin 16) (14 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_14_15 : (B_scc * A_scc) (14 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_14 : ∀ j, (B_scc * A_scc) (14 : Fin 16) j = if (14 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_14_0
  · simpa using cell_14_1
  · simpa using cell_14_2
  · simpa using cell_14_3
  · simpa using cell_14_4
  · simpa using cell_14_5
  · simpa using cell_14_6
  · simpa using cell_14_7
  · simpa using cell_14_8
  · simpa using cell_14_9
  · simpa using cell_14_10
  · simpa using cell_14_11
  · simpa using cell_14_12
  · simpa using cell_14_13
  · simpa using cell_14_14
  · simpa using cell_14_15
#print axioms row_14

theorem cell_15_0 : (B_scc * A_scc) (15 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_1 : (B_scc * A_scc) (15 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_2 : (B_scc * A_scc) (15 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_3 : (B_scc * A_scc) (15 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_4 : (B_scc * A_scc) (15 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_5 : (B_scc * A_scc) (15 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_6 : (B_scc * A_scc) (15 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_7 : (B_scc * A_scc) (15 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_8 : (B_scc * A_scc) (15 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_9 : (B_scc * A_scc) (15 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_10 : (B_scc * A_scc) (15 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_11 : (B_scc * A_scc) (15 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_12 : (B_scc * A_scc) (15 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_13 : (B_scc * A_scc) (15 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_14 : (B_scc * A_scc) (15 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_15_15 : (B_scc * A_scc) (15 : Fin 16) (15 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_15 : ∀ j, (B_scc * A_scc) (15 : Fin 16) j = if (15 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_15_0
  · simpa using cell_15_1
  · simpa using cell_15_2
  · simpa using cell_15_3
  · simpa using cell_15_4
  · simpa using cell_15_5
  · simpa using cell_15_6
  · simpa using cell_15_7
  · simpa using cell_15_8
  · simpa using cell_15_9
  · simpa using cell_15_10
  · simpa using cell_15_11
  · simpa using cell_15_12
  · simpa using cell_15_13
  · simpa using cell_15_14
  · simpa using cell_15_15
#print axioms row_15

end R752SCC12Rows04
