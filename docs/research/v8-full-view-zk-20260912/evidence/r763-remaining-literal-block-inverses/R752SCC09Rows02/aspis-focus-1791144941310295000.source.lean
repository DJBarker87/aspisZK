/- SCC 9, rows [4, 5, 6, 7]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC09Matrix
import Mathlib.Tactic

namespace R752SCC09Rows02
open R752SCC09Matrix

theorem cell_4_0 : (B_scc * A_scc) (4 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_1 : (B_scc * A_scc) (4 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_2 : (B_scc * A_scc) (4 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_3 : (B_scc * A_scc) (4 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_4 : (B_scc * A_scc) (4 : Fin 16) (4 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_5 : (B_scc * A_scc) (4 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_6 : (B_scc * A_scc) (4 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_7 : (B_scc * A_scc) (4 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_8 : (B_scc * A_scc) (4 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_9 : (B_scc * A_scc) (4 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_10 : (B_scc * A_scc) (4 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_11 : (B_scc * A_scc) (4 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_12 : (B_scc * A_scc) (4 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_13 : (B_scc * A_scc) (4 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_14 : (B_scc * A_scc) (4 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_15 : (B_scc * A_scc) (4 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_4 : ∀ j, (B_scc * A_scc) (4 : Fin 16) j = if (4 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_4_0
  · simpa using cell_4_1
  · simpa using cell_4_2
  · simpa using cell_4_3
  · simpa using cell_4_4
  · simpa using cell_4_5
  · simpa using cell_4_6
  · simpa using cell_4_7
  · simpa using cell_4_8
  · simpa using cell_4_9
  · simpa using cell_4_10
  · simpa using cell_4_11
  · simpa using cell_4_12
  · simpa using cell_4_13
  · simpa using cell_4_14
  · simpa using cell_4_15
#print axioms row_4

theorem cell_5_0 : (B_scc * A_scc) (5 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_1 : (B_scc * A_scc) (5 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_2 : (B_scc * A_scc) (5 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_3 : (B_scc * A_scc) (5 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_4 : (B_scc * A_scc) (5 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_5 : (B_scc * A_scc) (5 : Fin 16) (5 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_6 : (B_scc * A_scc) (5 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_7 : (B_scc * A_scc) (5 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_8 : (B_scc * A_scc) (5 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_9 : (B_scc * A_scc) (5 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_10 : (B_scc * A_scc) (5 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_11 : (B_scc * A_scc) (5 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_12 : (B_scc * A_scc) (5 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_13 : (B_scc * A_scc) (5 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_14 : (B_scc * A_scc) (5 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_15 : (B_scc * A_scc) (5 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_5 : ∀ j, (B_scc * A_scc) (5 : Fin 16) j = if (5 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_5_0
  · simpa using cell_5_1
  · simpa using cell_5_2
  · simpa using cell_5_3
  · simpa using cell_5_4
  · simpa using cell_5_5
  · simpa using cell_5_6
  · simpa using cell_5_7
  · simpa using cell_5_8
  · simpa using cell_5_9
  · simpa using cell_5_10
  · simpa using cell_5_11
  · simpa using cell_5_12
  · simpa using cell_5_13
  · simpa using cell_5_14
  · simpa using cell_5_15
#print axioms row_5

theorem cell_6_0 : (B_scc * A_scc) (6 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_1 : (B_scc * A_scc) (6 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_2 : (B_scc * A_scc) (6 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_3 : (B_scc * A_scc) (6 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_4 : (B_scc * A_scc) (6 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_5 : (B_scc * A_scc) (6 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_6 : (B_scc * A_scc) (6 : Fin 16) (6 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_7 : (B_scc * A_scc) (6 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_8 : (B_scc * A_scc) (6 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_9 : (B_scc * A_scc) (6 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_10 : (B_scc * A_scc) (6 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_11 : (B_scc * A_scc) (6 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_12 : (B_scc * A_scc) (6 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_13 : (B_scc * A_scc) (6 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_14 : (B_scc * A_scc) (6 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_15 : (B_scc * A_scc) (6 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_6 : ∀ j, (B_scc * A_scc) (6 : Fin 16) j = if (6 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_6_0
  · simpa using cell_6_1
  · simpa using cell_6_2
  · simpa using cell_6_3
  · simpa using cell_6_4
  · simpa using cell_6_5
  · simpa using cell_6_6
  · simpa using cell_6_7
  · simpa using cell_6_8
  · simpa using cell_6_9
  · simpa using cell_6_10
  · simpa using cell_6_11
  · simpa using cell_6_12
  · simpa using cell_6_13
  · simpa using cell_6_14
  · simpa using cell_6_15
#print axioms row_6

theorem cell_7_0 : (B_scc * A_scc) (7 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_1 : (B_scc * A_scc) (7 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_2 : (B_scc * A_scc) (7 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_3 : (B_scc * A_scc) (7 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_4 : (B_scc * A_scc) (7 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_5 : (B_scc * A_scc) (7 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_6 : (B_scc * A_scc) (7 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_7 : (B_scc * A_scc) (7 : Fin 16) (7 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_8 : (B_scc * A_scc) (7 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_9 : (B_scc * A_scc) (7 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_10 : (B_scc * A_scc) (7 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_11 : (B_scc * A_scc) (7 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_12 : (B_scc * A_scc) (7 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_13 : (B_scc * A_scc) (7 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_14 : (B_scc * A_scc) (7 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_15 : (B_scc * A_scc) (7 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_7 : ∀ j, (B_scc * A_scc) (7 : Fin 16) j = if (7 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_7_0
  · simpa using cell_7_1
  · simpa using cell_7_2
  · simpa using cell_7_3
  · simpa using cell_7_4
  · simpa using cell_7_5
  · simpa using cell_7_6
  · simpa using cell_7_7
  · simpa using cell_7_8
  · simpa using cell_7_9
  · simpa using cell_7_10
  · simpa using cell_7_11
  · simpa using cell_7_12
  · simpa using cell_7_13
  · simpa using cell_7_14
  · simpa using cell_7_15
#print axioms row_7

end R752SCC09Rows02
