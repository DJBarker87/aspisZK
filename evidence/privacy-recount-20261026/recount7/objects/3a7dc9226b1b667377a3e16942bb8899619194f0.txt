import R1Z.PV_Join_PublicCaller
import R1Z.ProverRw19AuditSource
import R1Z.ProverRw19AuditData
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_AuditProjection
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
open ProverRw19AuditValue ProverRw19AuditData

/-- The installed op229/P8 caller has the source guard's canonical successful
 audit. This theorem assumes no successful body result and no byte equation. -/
theorem public_body_good (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S),
    Good (PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro S store pub compiled v hash binding digest attempt s
  exact @ProverRw19AuditSource.body _ (PV_Join_PublicCaller.selected base ops)
    S store pub compiled v hash (ProverRwOuterContextModel.context digest attempt.mask_nonce)
    binding attempt s

variable [ExternalTypes]
/-- The actual emitted attempt entry, including its public encoding, hash,
context and binding prefix, inherits the successful audit value. This is a
source guard theorem, not a mathematical byte-result equation. -/
theorem native_attempt_good (ops : ExternalFuns)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    letI : ExternalFuns := ops
    Good (prover.prove_masked_attempt pub compiled v hash attempt store) := by
  letI : ExternalFuns := ops
  unfold prover.prove_masked_attempt
  repeat' first
    | exact ProverRw19AuditSource.body _ _ _ _ _ _ _ _ _
    | exact residual _ _
    | apply bind_good; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split

/-- The full audit observation also includes error/failure/divergence status.
It follows only once the independently defined model's byte equation is proved. -/
theorem whole_of_bytes (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S)
    (modelBytes : Result ByteStatus),
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s)) = modelBytes →
    data (PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s) =
      attachAudit modelBytes := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro S store pub compiled v hash binding digest attempt s modelBytes bytes
  exact data_of_bytes _ modelBytes
    (public_body_good base ops store pub compiled v hash binding digest attempt s) bytes

#print axioms public_body_good
#print axioms native_attempt_good
#print axioms whole_of_bytes
end R1Z.PV_Join_AuditProjection
