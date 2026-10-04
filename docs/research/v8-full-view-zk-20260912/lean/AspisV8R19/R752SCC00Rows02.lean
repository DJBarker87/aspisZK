/- SCC 0, rows [4, 5]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC00Matrix
import Mathlib.Tactic

namespace R752SCC00Rows02
open R752SCC00Matrix

theorem cell_4_0 : (B_scc * A_scc) (4 : Fin 6) (0 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_1 : (B_scc * A_scc) (4 : Fin 6) (1 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_2 : (B_scc * A_scc) (4 : Fin 6) (2 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_3 : (B_scc * A_scc) (4 : Fin 6) (3 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_4 : (B_scc * A_scc) (4 : Fin 6) (4 : Fin 6) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_4_5 : (B_scc * A_scc) (4 : Fin 6) (5 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_4 : ∀ j, (B_scc * A_scc) (4 : Fin 6) j = if (4 : Fin 6) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_4_0
  · simpa using cell_4_1
  · simpa using cell_4_2
  · simpa using cell_4_3
  · simpa using cell_4_4
  · simpa using cell_4_5
#print axioms row_4

theorem cell_5_0 : (B_scc * A_scc) (5 : Fin 6) (0 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_1 : (B_scc * A_scc) (5 : Fin 6) (1 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_2 : (B_scc * A_scc) (5 : Fin 6) (2 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_3 : (B_scc * A_scc) (5 : Fin 6) (3 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_4 : (B_scc * A_scc) (5 : Fin 6) (4 : Fin 6) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_5_5 : (B_scc * A_scc) (5 : Fin 6) (5 : Fin 6) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_5 : ∀ j, (B_scc * A_scc) (5 : Fin 6) j = if (5 : Fin 6) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_5_0
  · simpa using cell_5_1
  · simpa using cell_5_2
  · simpa using cell_5_3
  · simpa using cell_5_4
  · simpa using cell_5_5
#print axioms row_5

end R752SCC00Rows02
