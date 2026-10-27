import GExp_IdealValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_RowsBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_QueryBudget MultiproofConeRef

theorem rows (fuel : Nat) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    bounded fuel (Port9OR_P6Rows.rows fuel s physical i w) := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [Port9OR_P6Rows.rows]
    split
    · exact pure_bound _ _
    · exact lift_bound _ _
  | succ fuel ih =>
    simp only [Port9OR_P6Rows.rows]
    split
    · exact pure_bound _ _
    · query_budget_then 1
      · omega
      · exact GExp_NodeBudget.node _ _ _ _
      · intro out
        cases out with
        | Stop stopped => exact pure_bound _ _
        | Next next ni nw => simpa only [Nat.add_sub_cancel] using ih next ni nw

#print axioms rows
end AspisR1.GExp_RowsBudget
end
