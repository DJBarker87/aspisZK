/- SCC 33, rows [4, 5, 6, 7]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC33Matrix
import Mathlib.Tactic

namespace R752SCC33Rows02
open R752SCC33Matrix

theorem cell_4_0 : (B_scc * A_scc) (4 : Fin 8) (0 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_1 : (B_scc * A_scc) (4 : Fin 8) (1 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_2 : (B_scc * A_scc) (4 : Fin 8) (2 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_3 : (B_scc * A_scc) (4 : Fin 8) (3 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_4 : (B_scc * A_scc) (4 : Fin 8) (4 : Fin 8) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_5 : (B_scc * A_scc) (4 : Fin 8) (5 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_6 : (B_scc * A_scc) (4 : Fin 8) (6 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_7 : (B_scc * A_scc) (4 : Fin 8) (7 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_4 : ∀ j, (B_scc * A_scc) (4 : Fin 8) j = if (4 : Fin 8) = j then (1 : M) else 0 := by
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
#print axioms row_4

theorem cell_5_0 : (B_scc * A_scc) (5 : Fin 8) (0 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_1 : (B_scc * A_scc) (5 : Fin 8) (1 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_2 : (B_scc * A_scc) (5 : Fin 8) (2 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_3 : (B_scc * A_scc) (5 : Fin 8) (3 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_4 : (B_scc * A_scc) (5 : Fin 8) (4 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_5 : (B_scc * A_scc) (5 : Fin 8) (5 : Fin 8) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_6 : (B_scc * A_scc) (5 : Fin 8) (6 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_7 : (B_scc * A_scc) (5 : Fin 8) (7 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_5 : ∀ j, (B_scc * A_scc) (5 : Fin 8) j = if (5 : Fin 8) = j then (1 : M) else 0 := by
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
#print axioms row_5

theorem cell_6_0 : (B_scc * A_scc) (6 : Fin 8) (0 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_1 : (B_scc * A_scc) (6 : Fin 8) (1 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_2 : (B_scc * A_scc) (6 : Fin 8) (2 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_3 : (B_scc * A_scc) (6 : Fin 8) (3 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_4 : (B_scc * A_scc) (6 : Fin 8) (4 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_5 : (B_scc * A_scc) (6 : Fin 8) (5 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_6 : (B_scc * A_scc) (6 : Fin 8) (6 : Fin 8) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_6_7 : (B_scc * A_scc) (6 : Fin 8) (7 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_6 : ∀ j, (B_scc * A_scc) (6 : Fin 8) j = if (6 : Fin 8) = j then (1 : M) else 0 := by
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
#print axioms row_6

theorem cell_7_0 : (B_scc * A_scc) (7 : Fin 8) (0 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_1 : (B_scc * A_scc) (7 : Fin 8) (1 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_2 : (B_scc * A_scc) (7 : Fin 8) (2 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_3 : (B_scc * A_scc) (7 : Fin 8) (3 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_4 : (B_scc * A_scc) (7 : Fin 8) (4 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_5 : (B_scc * A_scc) (7 : Fin 8) (5 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_6 : (B_scc * A_scc) (7 : Fin 8) (6 : Fin 8) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_7_7 : (B_scc * A_scc) (7 : Fin 8) (7 : Fin 8) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_7 : ∀ j, (B_scc * A_scc) (7 : Fin 8) j = if (7 : Fin 8) = j then (1 : M) else 0 := by
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
#print axioms row_7

end R752SCC33Rows02
