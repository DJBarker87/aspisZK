import R1Z.PV_RunJoin_NativeAfterAudit55
import R1Z.PV_RunJoin_NativeAfterBuildRel55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAfterAuditRel55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_ResultRelation55 PV_RunJoin_NativeResult55
variable [ExternalTypes] [ExternalFuns]
theorem complete {A B T0 : Type} (R : A → B → Prop)
    (f : Phase → Result (core.result.Result A verifier.Error))
    (g : Phase → Result (core.result.Result B verifier.Error))
    (step : ∀ p,Rel (CoreRel R) (f p) (g p))
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
    Rel (Output R)
      (PV_RunJoin_NativeAfterAudit55.run f aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash reserved context noised maskOnly d g_ h1_padding audit store)
      (PV_RunJoin_NativeAfterAudit55.run g aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash reserved context noised maskOnly d g_ h1_padding audit store) := by
  unfold PV_RunJoin_NativeAfterAudit55.run
  apply PV_RunJoin_ResultRelation55.same_bind
  intro tag1
  apply PV_RunJoin_ResultRelation55.same_bind
  intro saltResult1
  cases saltResult1 with
  | Err e => exact PV_RunJoin_NativeResult55.error R _ _
  | Ok salts1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro tag2
    apply PV_RunJoin_ResultRelation55.same_bind
    intro saltResult2
    cases saltResult2 with
    | Err e => exact PV_RunJoin_NativeResult55.error R _ _
    | Ok salts2 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultRelation55.same_bind
      intro domainResult
      apply PV_RunJoin_ResultRelation55.same_bind
      intro mappedDomain
      cases mappedDomain with
      | Err e => exact PV_RunJoin_NativeResult55.error R _ _
      | Ok domain =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultRelation55.same_bind
        intro zero
        apply PV_RunJoin_ResultRelation55.same_bind
        intro messages
        apply PV_RunJoin_ResultRelation55.same_bind
        intro pair
        dsimp only [Aeneas.Std.uncurry]
        exact PV_RunJoin_NativeAfterBuildRel55.complete R f g step public1 variant hash pair.2 reserved context audit store pair.1
#print axioms complete
end R1Z.PV_RunJoin_NativeAfterAuditRel55
