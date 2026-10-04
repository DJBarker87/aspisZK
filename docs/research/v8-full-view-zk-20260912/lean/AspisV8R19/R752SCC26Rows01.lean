/- SCC 26, rows [0]; each scalar product is checked independently. -/
import AspisV8R19.R752SCC26Matrix
import Mathlib.Tactic

namespace R752SCC26Rows01
open R752SCC26Matrix

theorem cell_0_0 : (B_scc * A_scc) (0 : Fin 1) (0 : Fin 1) = (1 : M) := by
  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide

theorem row_0 : ∀ j, (B_scc * A_scc) (0 : Fin 1) j = if (0 : Fin 1) = j then (1 : M) else 0 := by
  intro j
  fin_cases j
  · simpa using cell_0_0
#print axioms row_0

end R752SCC26Rows01
