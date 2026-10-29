import R1Z.PV_RunJoin_NativeAfterAudit55
import R1Z.PV_RunJoin_CaptureFactorAfterBuild60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CaptureFactorAfterAudit60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_CaptureFactorRelation60
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes] [ExternalFuns]
theorem complete {A T0 : Type}
    (f : Phase → Result (core.result.Result A verifier.Error))
    (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g_ h1_padding : Array aspis_core.field.QM31 1024#usize)
    (audit : prover.MaskedFixtureAudit) (store : T0) :
    Rel f
      (PV_RunJoin_NativeAfterAudit55.run f aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash reserved context noised maskOnly d g_ h1_padding audit store)
      (PV_RunJoin_NativeAfterAudit55.run capture aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash reserved context noised maskOnly d g_ h1_padding audit store) := by
  unfold PV_RunJoin_NativeAfterAudit55.run
  apply PV_RunJoin_CaptureFactorRelation60.same_bind
  intro tag1
  apply PV_RunJoin_CaptureFactorRelation60.same_bind
  intro saltResult1
  cases saltResult1 with
  | Err e => exact PV_RunJoin_CaptureFactorRelation60.error f _ _
  | Ok salts1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_CaptureFactorRelation60.same_bind
    intro tag2
    apply PV_RunJoin_CaptureFactorRelation60.same_bind
    intro saltResult2
    cases saltResult2 with
    | Err e => exact PV_RunJoin_CaptureFactorRelation60.error f _ _
    | Ok salts2 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_CaptureFactorRelation60.same_bind
      intro domainResult
      apply PV_RunJoin_CaptureFactorRelation60.same_bind
      intro mappedDomain
      cases mappedDomain with
      | Err e => exact PV_RunJoin_CaptureFactorRelation60.error f _ _
      | Ok domain =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_CaptureFactorRelation60.same_bind
        intro zero
        apply PV_RunJoin_CaptureFactorRelation60.same_bind
        intro messages
        apply PV_RunJoin_CaptureFactorRelation60.same_bind
        intro pair
        dsimp only [Aeneas.Std.uncurry]
        exact PV_RunJoin_CaptureFactorAfterBuild60.complete f public1 variant hash pair.2 reserved context audit store pair.1
#print axioms complete
end R1Z.PV_RunJoin_CaptureFactorAfterAudit60
