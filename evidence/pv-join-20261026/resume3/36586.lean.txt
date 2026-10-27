import R1Z.PV_Join_AuditProjection
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicDataIff
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
open ProverRw19AuditData

/-- The source guard supplies the complete audit/status observation once the
independent model byte equation is available. Neither fixture byte equation
nor a concrete mathematical model instance is assumed to have been proved. -/
theorem refinement_of_bytes (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (modelBytes : Result ByteStatus),
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s)) = modelBytes →
    PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s =
      ProverRwBodyCandidateData.withState after (attachAudit modelBytes) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro S store pub compiled v hash binding digest attempt s after accepted reservation modelBytes bytes
  exact PV_Join_PublicCaller.refinement_of_data base ops store pub compiled v hash
    binding digest attempt s after accepted reservation (attachAudit modelBytes)
    (PV_Join_AuditProjection.whole_of_bytes base ops store pub compiled v hash
      binding digest attempt s modelBytes bytes)

/-- Exact criterion, preserving Err/failure/divergence and the returned store.
The right hand side is still the unproved independent byte equation. -/
theorem criterion (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (modelBytes : Result ByteStatus),
    PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s =
      ProverRwBodyCandidateData.withState after (attachAudit modelBytes) ↔
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (PV_Join_PublicCaller.execute base ops store pub compiled v hash binding digest attempt s)) = modelBytes := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro S store pub compiled v hash binding digest attempt s after accepted reservation modelBytes
  constructor
  · intro whole
    rw [whole,ProverRwBodyCandidateData.data_withState]
    exact ProverRw19AuditData.bytes modelBytes
  · exact refinement_of_bytes base ops store pub compiled v hash
      binding digest attempt s after accepted reservation modelBytes

#print axioms refinement_of_bytes
#print axioms criterion
end R1Z.PV_Join_PublicDataIff
