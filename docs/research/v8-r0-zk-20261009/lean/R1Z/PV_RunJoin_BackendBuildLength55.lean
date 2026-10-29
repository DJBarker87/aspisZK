import R1Z.PV_RunJoin_BackendC1Length55
import R1Z.PV_RunJoin_BackendC2Length55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendBuildLength55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem complete
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array aspis_core.field.QM31 1024#usize)
    (backend : prover.Backend) (hash : aspis_core.digest.LegacyHashFn)
    (variant : transport.Variant) (hlen : backend.messages.length=29) :
    Post (fun next => next.2.messages.length=29)
      (host_semantic.build_with_material aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
        public1 compiled noised maskOnly d g padding backend hash variant) := by
  unfold host_semantic.build_with_material host_semantic.build_with_helper_mode
  repeat' (try (simp only [Aeneas.Std.uncurry,lift,bind_tc_ok]); first
    | exact hlen
    | exact length
    | assumption
    | apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC1Length55.complete _ _ _ (by assumption)); intro value length
    | apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC2Length55.complete _ _ _ (by assumption)); intro value length
    | apply PV_RunJoin_ResultPost41.bind; intro value
    | split)
#print axioms complete
end R1Z.PV_RunJoin_BackendBuildLength55
