/- SCC 0, rows [0, 1, 2, 3]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC00Matrix
import Mathlib.Tactic

namespace R752SCC00Rows01
open R752SCC00Matrix

theorem cell_0_0 : (B_scc * A_scc) (0 : Fin 6) (0 : Fin 6) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_1 : (B_scc * A_scc) (0 : Fin 6) (1 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_2 : (B_scc * A_scc) (0 : Fin 6) (2 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_3 : (B_scc * A_scc) (0 : Fin 6) (3 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_4 : (B_scc * A_scc) (0 : Fin 6) (4 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_5 : (B_scc * A_scc) (0 : Fin 6) (5 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_0 : ∀ j, (B_scc * A_scc) (0 : Fin 6) j = if (0 : Fin 6) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_0_0
  · simpa using cell_0_1
  · simpa using cell_0_2
  · simpa using cell_0_3
  · simpa using cell_0_4
  · simpa using cell_0_5
#print axioms row_0

theorem cell_1_0 : (B_scc * A_scc) (1 : Fin 6) (0 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_1 : (B_scc * A_scc) (1 : Fin 6) (1 : Fin 6) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_2 : (B_scc * A_scc) (1 : Fin 6) (2 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_3 : (B_scc * A_scc) (1 : Fin 6) (3 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_4 : (B_scc * A_scc) (1 : Fin 6) (4 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_5 : (B_scc * A_scc) (1 : Fin 6) (5 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_1 : ∀ j, (B_scc * A_scc) (1 : Fin 6) j = if (1 : Fin 6) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_1_0
  · simpa using cell_1_1
  · simpa using cell_1_2
  · simpa using cell_1_3
  · simpa using cell_1_4
  · simpa using cell_1_5
#print axioms row_1

theorem cell_2_0 : (B_scc * A_scc) (2 : Fin 6) (0 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_1 : (B_scc * A_scc) (2 : Fin 6) (1 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_2 : (B_scc * A_scc) (2 : Fin 6) (2 : Fin 6) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_3 : (B_scc * A_scc) (2 : Fin 6) (3 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_4 : (B_scc * A_scc) (2 : Fin 6) (4 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_5 : (B_scc * A_scc) (2 : Fin 6) (5 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_2 : ∀ j, (B_scc * A_scc) (2 : Fin 6) j = if (2 : Fin 6) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_2_0
  · simpa using cell_2_1
  · simpa using cell_2_2
  · simpa using cell_2_3
  · simpa using cell_2_4
  · simpa using cell_2_5
#print axioms row_2

theorem cell_3_0 : (B_scc * A_scc) (3 : Fin 6) (0 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_1 : (B_scc * A_scc) (3 : Fin 6) (1 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_2 : (B_scc * A_scc) (3 : Fin 6) (2 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_3 : (B_scc * A_scc) (3 : Fin 6) (3 : Fin 6) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_4 : (B_scc * A_scc) (3 : Fin 6) (4 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_3_5 : (B_scc * A_scc) (3 : Fin 6) (5 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_3 : ∀ j, (B_scc * A_scc) (3 : Fin 6) j = if (3 : Fin 6) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_3_0
  · simpa using cell_3_1
  · simpa using cell_3_2
  · simpa using cell_3_3
  · simpa using cell_3_4
  · simpa using cell_3_5
#print axioms row_3

end R752SCC00Rows01
