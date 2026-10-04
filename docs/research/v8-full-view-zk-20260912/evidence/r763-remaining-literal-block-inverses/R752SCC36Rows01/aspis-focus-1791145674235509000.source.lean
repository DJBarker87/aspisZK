/- SCC 36, rows [0, 1, 2]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC36Matrix
import Mathlib.Tactic

namespace R752SCC36Rows01
open R752SCC36Matrix

theorem cell_0_0 : (B_scc * A_scc) (0 : Fin 3) (0 : Fin 3) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_1 : (B_scc * A_scc) (0 : Fin 3) (1 : Fin 3) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_2 : (B_scc * A_scc) (0 : Fin 3) (2 : Fin 3) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_0 : ∀ j, (B_scc * A_scc) (0 : Fin 3) j = if (0 : Fin 3) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_0_0
  · simpa using cell_0_1
  · simpa using cell_0_2
#print axioms row_0

theorem cell_1_0 : (B_scc * A_scc) (1 : Fin 3) (0 : Fin 3) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_1 : (B_scc * A_scc) (1 : Fin 3) (1 : Fin 3) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_2 : (B_scc * A_scc) (1 : Fin 3) (2 : Fin 3) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_1 : ∀ j, (B_scc * A_scc) (1 : Fin 3) j = if (1 : Fin 3) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_1_0
  · simpa using cell_1_1
  · simpa using cell_1_2
#print axioms row_1

theorem cell_2_0 : (B_scc * A_scc) (2 : Fin 3) (0 : Fin 3) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_1 : (B_scc * A_scc) (2 : Fin 3) (1 : Fin 3) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_2_2 : (B_scc * A_scc) (2 : Fin 3) (2 : Fin 3) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_2 : ∀ j, (B_scc * A_scc) (2 : Fin 3) j = if (2 : Fin 3) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_2_0
  · simpa using cell_2_1
  · simpa using cell_2_2
#print axioms row_2

end R752SCC36Rows01
