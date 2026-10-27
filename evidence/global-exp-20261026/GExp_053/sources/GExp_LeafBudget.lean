import GExp_BudgetTactic
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_LeafBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_QueryBudget

theorem codeFor (o : Slice U8) (tag : U8) (vs ve ss se : Usize) :
    bounded 1 (Port4B_LeafCode.codeFor o tag vs ve ss se) := by
  unfold Port4B_LeafCode.codeFor
  apply step_bound; intro salt
  apply step_bound; intro value
  exact read_bound _

theorem leaf (kind : Usize) (o : Slice U8) : bounded 1 (Port4B_LeafCode.code kind o) := by
  unfold Port4B_LeafCode.code
  split
  · exact codeFor _ _ _ _ _ _
  · split <;> exact codeFor _ _ _ _ _ _

#print axioms codeFor
#print axioms leaf
end AspisR1.GExp_LeafBudget
end
