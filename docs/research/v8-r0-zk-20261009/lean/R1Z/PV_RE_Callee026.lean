import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee026
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_tree.node_count` (callee `host_tree.check_indices`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (indices : Slice Std.U32) :
  ∃ next, host_tree.node_count (indices := indices) =
    (host_tree.check_indices indices >>= next) := by
  unfold host_tree.node_count
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee026
