/- SCC 9, rows [0, 1, 2, 3]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC09Matrix
import Mathlib.Tactic

namespace R752SCC09Rows01
open R752SCC09Matrix

theorem cell_0_0 : (B_scc * A_scc) (0 : Fin 16) (0 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_1 : (B_scc * A_scc) (0 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_2 : (B_scc * A_scc) (0 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_3 : (B_scc * A_scc) (0 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_4 : (B_scc * A_scc) (0 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_5 : (B_scc * A_scc) (0 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_6 : (B_scc * A_scc) (0 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_7 : (B_scc * A_scc) (0 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_8 : (B_scc * A_scc) (0 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_9 : (B_scc * A_scc) (0 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_10 : (B_scc * A_scc) (0 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_11 : (B_scc * A_scc) (0 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_12 : (B_scc * A_scc) (0 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_13 : (B_scc * A_scc) (0 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_14 : (B_scc * A_scc) (0 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_15 : (B_scc * A_scc) (0 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_0 : ∀ j, (B_scc * A_scc) (0 : Fin 16) j = if (0 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_0_0
  · simpa using cell_0_1
  · simpa using cell_0_2
  · simpa using cell_0_3
  · simpa using cell_0_4
  · simpa using cell_0_5
  · simpa using cell_0_6
  · simpa using cell_0_7
  · simpa using cell_0_8
  · simpa using cell_0_9
  · simpa using cell_0_10
  · simpa using cell_0_11
  · simpa using cell_0_12
  · simpa using cell_0_13
  · simpa using cell_0_14
  · simpa using cell_0_15
#print axioms row_0

theorem cell_1_0 : (B_scc * A_scc) (1 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_1 : (B_scc * A_scc) (1 : Fin 16) (1 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_2 : (B_scc * A_scc) (1 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_3 : (B_scc * A_scc) (1 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_4 : (B_scc * A_scc) (1 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_5 : (B_scc * A_scc) (1 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_6 : (B_scc * A_scc) (1 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_7 : (B_scc * A_scc) (1 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_8 : (B_scc * A_scc) (1 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_9 : (B_scc * A_scc) (1 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_10 : (B_scc * A_scc) (1 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_11 : (B_scc * A_scc) (1 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_12 : (B_scc * A_scc) (1 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_13 : (B_scc * A_scc) (1 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_14 : (B_scc * A_scc) (1 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_15 : (B_scc * A_scc) (1 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_1 : ∀ j, (B_scc * A_scc) (1 : Fin 16) j = if (1 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_1_0
  · simpa using cell_1_1
  · simpa using cell_1_2
  · simpa using cell_1_3
  · simpa using cell_1_4
  · simpa using cell_1_5
  · simpa using cell_1_6
  · simpa using cell_1_7
  · simpa using cell_1_8
  · simpa using cell_1_9
  · simpa using cell_1_10
  · simpa using cell_1_11
  · simpa using cell_1_12
  · simpa using cell_1_13
  · simpa using cell_1_14
  · simpa using cell_1_15
#print axioms row_1

theorem cell_2_0 : (B_scc * A_scc) (2 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_1 : (B_scc * A_scc) (2 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_2 : (B_scc * A_scc) (2 : Fin 16) (2 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_3 : (B_scc * A_scc) (2 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_4 : (B_scc * A_scc) (2 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_5 : (B_scc * A_scc) (2 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_6 : (B_scc * A_scc) (2 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_7 : (B_scc * A_scc) (2 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_8 : (B_scc * A_scc) (2 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_9 : (B_scc * A_scc) (2 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_10 : (B_scc * A_scc) (2 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_11 : (B_scc * A_scc) (2 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_12 : (B_scc * A_scc) (2 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_13 : (B_scc * A_scc) (2 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_14 : (B_scc * A_scc) (2 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_15 : (B_scc * A_scc) (2 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_2 : ∀ j, (B_scc * A_scc) (2 : Fin 16) j = if (2 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_2_0
  · simpa using cell_2_1
  · simpa using cell_2_2
  · simpa using cell_2_3
  · simpa using cell_2_4
  · simpa using cell_2_5
  · simpa using cell_2_6
  · simpa using cell_2_7
  · simpa using cell_2_8
  · simpa using cell_2_9
  · simpa using cell_2_10
  · simpa using cell_2_11
  · simpa using cell_2_12
  · simpa using cell_2_13
  · simpa using cell_2_14
  · simpa using cell_2_15
#print axioms row_2

theorem cell_3_0 : (B_scc * A_scc) (3 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_1 : (B_scc * A_scc) (3 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_2 : (B_scc * A_scc) (3 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_3 : (B_scc * A_scc) (3 : Fin 16) (3 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_4 : (B_scc * A_scc) (3 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_5 : (B_scc * A_scc) (3 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_6 : (B_scc * A_scc) (3 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_7 : (B_scc * A_scc) (3 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_8 : (B_scc * A_scc) (3 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_9 : (B_scc * A_scc) (3 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_10 : (B_scc * A_scc) (3 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_11 : (B_scc * A_scc) (3 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_12 : (B_scc * A_scc) (3 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_13 : (B_scc * A_scc) (3 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_14 : (B_scc * A_scc) (3 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_15 : (B_scc * A_scc) (3 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_3 : ∀ j, (B_scc * A_scc) (3 : Fin 16) j = if (3 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_3_0
  · simpa using cell_3_1
  · simpa using cell_3_2
  · simpa using cell_3_3
  · simpa using cell_3_4
  · simpa using cell_3_5
  · simpa using cell_3_6
  · simpa using cell_3_7
  · simpa using cell_3_8
  · simpa using cell_3_9
  · simpa using cell_3_10
  · simpa using cell_3_11
  · simpa using cell_3_12
  · simpa using cell_3_13
  · simpa using cell_3_14
  · simpa using cell_3_15
#print axioms row_3

end R752SCC09Rows01
