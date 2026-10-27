import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee034
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.derive_private_salt_step` (callee `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) (index : Std.U32) (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
  ∃ next, prover.derive_private_salt_step (reserved := reserved) (context := context) (hash := hash) (tag := tag) (index := index) (salts := salts) =
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt
      reserved hash context tag index >>= next) := by
  unfold prover.derive_private_salt_step
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee034
