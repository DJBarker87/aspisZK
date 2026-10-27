import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix035
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.prove_masked_attempt` (op226).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  ∃ next, @prover.prove_masked_attempt _ _ public1 compiled variant hash attempt nonce_store =
    (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      public1 >>= next) := by
  unfold prover.prove_masked_attempt
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix035
