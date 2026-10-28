import R1Z.ProverRw19AuditValue
import R1Z.ProverRwBodyStore
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19AuditSource
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19AuditValue
variable [ExternalTypes] [ExternalFuns]

-- Prove the successful audit value from the guards of the actual emitted
-- continuation. Primitive computations remain arbitrary Results; no success
-- or source-to-model equality is assumed for any callback.
theorem continuation {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (r : core.result.Result
      (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
        aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (after : S) :
    Good (ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after) := by
  unfold ProverRwBodyStoreSource.afterReserve
  repeat' first
    | exact rejected _ _
    | exact residual _ _
    | apply successful <;> simp_all <;> scalar_tac
    | apply bind_good; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split

theorem body {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    Good (prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s) := by
  rw [ProverRwBodyStore.factor]
  apply bind_good
  rintro ⟨r, after⟩
  exact continuation store pub compiled v hash context binding attempt r after

#print axioms continuation
#print axioms body
end R1Z.ProverRw19AuditSource
