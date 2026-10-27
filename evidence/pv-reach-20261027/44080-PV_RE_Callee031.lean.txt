import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee031
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.append_node_slots` (callee `prover.append_node_slot`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment) (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree) (queries : Array Std.U32 22#usize) :
  ∃ next, prover.append_node_slots (out := out) (cc1 := cc1) (cc2 := cc2) (tree := tree) (queries := queries) =
    (prover.append_node_slot out cc1 cc2 tree queries 0#usize 0#usize >>= next) := by
  unfold prover.append_node_slots
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee031
