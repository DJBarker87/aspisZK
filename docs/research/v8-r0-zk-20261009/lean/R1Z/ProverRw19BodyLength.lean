import R1Z.ProverRw19BodyLengthValue
import R1Z.ProverRw19SemanticLength
import R1Z.ProverRwBodyStore
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19BodyLength
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19BodyLengthValue
variable [ExternalTypes] [ExternalFuns]

-- Successful proof length follows the actual publication guard through the
-- emitted continuation. No concrete loops or arithmetic cells are evaluated.
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
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError) (after : S) (size : Usize) (P_proof_size : compact.PROOF_BYTES = ok size) :
    HasLength size.val (ProverRwBodyStoreSource.afterReserve store pub compiled v hash context binding attempt r after) := by
  unfold ProverRwBodyStoreSource.afterReserve
  repeat' first
    | exact rejected _ _ _
    | exact residual _ _ _
    | apply finish_good; exact ProverRw19SemanticLength.proof _ _ _ _ _ _ _ size P_proof_size
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
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S)
    (size : Usize) (P_proof_size : compact.PROOF_BYTES = ok size) :
    HasLength size.val (prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s) := by
  rw [ProverRwBodyStore.factor]
  apply bind_good
  rintro ⟨r, after⟩
  exact continuation store pub compiled v hash context binding attempt r after size P_proof_size

#print axioms continuation
#print axioms body
end R1Z.ProverRw19BodyLength
