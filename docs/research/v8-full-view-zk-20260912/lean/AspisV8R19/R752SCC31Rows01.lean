/- SCC 31, rows [0, 1]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC31Matrix
import Mathlib.Tactic

namespace R752SCC31Rows01
open R752SCC31Matrix

theorem cell_0_0 : (B_scc * A_scc) (0 : Fin 2) (0 : Fin 2) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_0_1 : (B_scc * A_scc) (0 : Fin 2) (1 : Fin 2) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_0 : ∀ j, (B_scc * A_scc) (0 : Fin 2) j = if (0 : Fin 2) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_0_0
  · simpa using cell_0_1
#print axioms row_0

theorem cell_1_0 : (B_scc * A_scc) (1 : Fin 2) (0 : Fin 2) = (0 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem cell_1_1 : (B_scc * A_scc) (1 : Fin 2) (1 : Fin 2) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_1 : ∀ j, (B_scc * A_scc) (1 : Fin 2) j = if (1 : Fin 2) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_1_0
  · simpa using cell_1_1
#print axioms row_1

end R752SCC31Rows01
