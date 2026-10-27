import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix027
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_tree.BinaryTree.root` (op235).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : host_tree.BinaryTree) :
  ∃ next, @host_tree.BinaryTree.root _ _ self =
    (multiproof.LEAF_BITS >>= next) := by
  unfold host_tree.BinaryTree.root
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix027
