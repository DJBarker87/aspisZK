import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee006
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt` (callee `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (tree_tag : Std.U8) (leaf_index : Std.U32) :
  ∃ next, aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt (self := self) (hash := hash) (context := context) (tree_tag := tree_tag) (leaf_index := leaf_index) =
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context >>= next) := by
  unfold aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee006
