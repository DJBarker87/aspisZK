import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicFailure4
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- An actual extracted rejection prefix. This is conditional on a source
callback failure, so it excludes no row on all admitted fixture inputs. -/
theorem fail_public (ops : ExternalFuns)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (failed : ops.op226 pub = .fail .panic) :
    @prover.prove_masked_attempt _ ops pub compiled v hash attempt store = .fail .panic := by
  unfold prover.prove_masked_attempt
  simp only [aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes, failed, bind_tc_fail]
#print axioms fail_public
end R1Z.PV_Join_PublicFailure4
