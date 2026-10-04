/- SCC 9, rows [8, 9, 10, 11]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC09Matrix
import Mathlib.Tactic

namespace R752SCC09Rows03
open R752SCC09Matrix

theorem cell_8_0 : (B_scc * A_scc) (8 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_1 : (B_scc * A_scc) (8 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_2 : (B_scc * A_scc) (8 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_3 : (B_scc * A_scc) (8 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_4 : (B_scc * A_scc) (8 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_5 : (B_scc * A_scc) (8 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_6 : (B_scc * A_scc) (8 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_7 : (B_scc * A_scc) (8 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_8 : (B_scc * A_scc) (8 : Fin 16) (8 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_9 : (B_scc * A_scc) (8 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_10 : (B_scc * A_scc) (8 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_11 : (B_scc * A_scc) (8 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_12 : (B_scc * A_scc) (8 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_13 : (B_scc * A_scc) (8 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_14 : (B_scc * A_scc) (8 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_8_15 : (B_scc * A_scc) (8 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_8 : ∀ j, (B_scc * A_scc) (8 : Fin 16) j = if (8 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_8_0
  · simpa using cell_8_1
  · simpa using cell_8_2
  · simpa using cell_8_3
  · simpa using cell_8_4
  · simpa using cell_8_5
  · simpa using cell_8_6
  · simpa using cell_8_7
  · simpa using cell_8_8
  · simpa using cell_8_9
  · simpa using cell_8_10
  · simpa using cell_8_11
  · simpa using cell_8_12
  · simpa using cell_8_13
  · simpa using cell_8_14
  · simpa using cell_8_15
#print axioms row_8

theorem cell_9_0 : (B_scc * A_scc) (9 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_1 : (B_scc * A_scc) (9 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_2 : (B_scc * A_scc) (9 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_3 : (B_scc * A_scc) (9 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_4 : (B_scc * A_scc) (9 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_5 : (B_scc * A_scc) (9 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_6 : (B_scc * A_scc) (9 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_7 : (B_scc * A_scc) (9 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_8 : (B_scc * A_scc) (9 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_9 : (B_scc * A_scc) (9 : Fin 16) (9 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_10 : (B_scc * A_scc) (9 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_11 : (B_scc * A_scc) (9 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_12 : (B_scc * A_scc) (9 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_13 : (B_scc * A_scc) (9 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_14 : (B_scc * A_scc) (9 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_9_15 : (B_scc * A_scc) (9 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_9 : ∀ j, (B_scc * A_scc) (9 : Fin 16) j = if (9 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_9_0
  · simpa using cell_9_1
  · simpa using cell_9_2
  · simpa using cell_9_3
  · simpa using cell_9_4
  · simpa using cell_9_5
  · simpa using cell_9_6
  · simpa using cell_9_7
  · simpa using cell_9_8
  · simpa using cell_9_9
  · simpa using cell_9_10
  · simpa using cell_9_11
  · simpa using cell_9_12
  · simpa using cell_9_13
  · simpa using cell_9_14
  · simpa using cell_9_15
#print axioms row_9

theorem cell_10_0 : (B_scc * A_scc) (10 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_1 : (B_scc * A_scc) (10 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_2 : (B_scc * A_scc) (10 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_3 : (B_scc * A_scc) (10 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_4 : (B_scc * A_scc) (10 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_5 : (B_scc * A_scc) (10 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_6 : (B_scc * A_scc) (10 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_7 : (B_scc * A_scc) (10 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_8 : (B_scc * A_scc) (10 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_9 : (B_scc * A_scc) (10 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_10 : (B_scc * A_scc) (10 : Fin 16) (10 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_11 : (B_scc * A_scc) (10 : Fin 16) (11 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_12 : (B_scc * A_scc) (10 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_13 : (B_scc * A_scc) (10 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_14 : (B_scc * A_scc) (10 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_10_15 : (B_scc * A_scc) (10 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_10 : ∀ j, (B_scc * A_scc) (10 : Fin 16) j = if (10 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_10_0
  · simpa using cell_10_1
  · simpa using cell_10_2
  · simpa using cell_10_3
  · simpa using cell_10_4
  · simpa using cell_10_5
  · simpa using cell_10_6
  · simpa using cell_10_7
  · simpa using cell_10_8
  · simpa using cell_10_9
  · simpa using cell_10_10
  · simpa using cell_10_11
  · simpa using cell_10_12
  · simpa using cell_10_13
  · simpa using cell_10_14
  · simpa using cell_10_15
#print axioms row_10

theorem cell_11_0 : (B_scc * A_scc) (11 : Fin 16) (0 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_1 : (B_scc * A_scc) (11 : Fin 16) (1 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_2 : (B_scc * A_scc) (11 : Fin 16) (2 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_3 : (B_scc * A_scc) (11 : Fin 16) (3 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_4 : (B_scc * A_scc) (11 : Fin 16) (4 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_5 : (B_scc * A_scc) (11 : Fin 16) (5 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_6 : (B_scc * A_scc) (11 : Fin 16) (6 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_7 : (B_scc * A_scc) (11 : Fin 16) (7 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_8 : (B_scc * A_scc) (11 : Fin 16) (8 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_9 : (B_scc * A_scc) (11 : Fin 16) (9 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_10 : (B_scc * A_scc) (11 : Fin 16) (10 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_11 : (B_scc * A_scc) (11 : Fin 16) (11 : Fin 16) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_12 : (B_scc * A_scc) (11 : Fin 16) (12 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_13 : (B_scc * A_scc) (11 : Fin 16) (13 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_14 : (B_scc * A_scc) (11 : Fin 16) (14 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_11_15 : (B_scc * A_scc) (11 : Fin 16) (15 : Fin 16) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_11 : ∀ j, (B_scc * A_scc) (11 : Fin 16) j = if (11 : Fin 16) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_11_0
  · simpa using cell_11_1
  · simpa using cell_11_2
  · simpa using cell_11_3
  · simpa using cell_11_4
  · simpa using cell_11_5
  · simpa using cell_11_6
  · simpa using cell_11_7
  · simpa using cell_11_8
  · simpa using cell_11_9
  · simpa using cell_11_10
  · simpa using cell_11_11
  · simpa using cell_11_12
  · simpa using cell_11_13
  · simpa using cell_11_14
  · simpa using cell_11_15
#print axioms row_11

end R752SCC09Rows03
