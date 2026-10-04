/- Row 28 of the exact R724 SCC-6 left-inverse candidate.
This target checks only these 39 entries; it does not connect the matrix to
source execution or prove the full block identity. -/
import AspisV8R19.R747JointBlock39Preflight
import Mathlib.Tactic

namespace R749JointBlock39Row28
open R747JointBlock39Preflight

theorem row28 : ∀ j : Fin 39,
    (B * A) 28 j = (1 : Matrix (Fin 39) (Fin 39) M) 28 j := by
  intro j
  fin_cases j <;>
    simp only [Matrix.one_apply] <;>
    simp only [Matrix.mul_apply, A, B, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero] <;>
    norm_num <;>
    decide

#print axioms row28

end R749JointBlock39Row28
