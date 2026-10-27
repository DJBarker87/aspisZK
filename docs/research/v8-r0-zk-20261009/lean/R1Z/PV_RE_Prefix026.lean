import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix026
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_tree.BinaryTree.multiproof` (op235).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : host_tree.BinaryTree) (indices : Slice Std.U32) :
  ∃ next, @host_tree.BinaryTree.multiproof _ _ self indices =
    (multiproof.LEAF_BITS >>= next) := by
  unfold host_tree.BinaryTree.multiproof
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix026
