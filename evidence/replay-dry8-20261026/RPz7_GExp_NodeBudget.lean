import RPz7_GExp_LeafBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_NodeBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_QueryBudget
open MultiproofConeRef

theorem parent (s : reference.Scratch) (left right : Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) :
    bounded 1 (Port9OR_P6Node.parent s left right ni cursor index w) := by
  constructor
  · decide
  · intro reply
    exact lift_bound _ _

theorem node (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    bounded 1 (Port9OR_P6Node.node s physical i w) := by
  unfold Port9OR_P6Node.node
  repeat' first
    | (solve | exact pure_bound _ _)
    | (solve | apply parent)
    | (apply step_bound;intro x)
    | split

#print axioms parent
#print axioms node
end AspisR1.GExp_NodeBudget
end
