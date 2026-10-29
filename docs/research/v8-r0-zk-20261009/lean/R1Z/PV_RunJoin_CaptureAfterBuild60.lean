import R1Z.PV_RunJoin_NativeAfterBuild55
import R1Z.PV_RunJoin_CaptureRelation60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CaptureAfterBuild60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_CaptureRelation60
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes] [ExternalFuns]
theorem complete {A T : Type}
    (f : Phase → Result (core.result.Result A verifier.Error))
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (r14 : core.result.Result (host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) r1_wire.Error) :
    Rel f
      (PV_RunJoin_NativeAfterBuild55.run f public1 variant hash backend reserved context audit store r14)
      (PV_RunJoin_NativeAfterBuild55.run capture public1 variant hash backend reserved context audit store r14) := by
  unfold PV_RunJoin_NativeAfterBuild55.run
  apply PV_RunJoin_CaptureRelation60.same_bind
  intro status
  cases status with
  | Err e => exact PV_RunJoin_CaptureRelation60.error f _ _
  | Ok sem =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_CaptureRelation60.same_bind
    intro column
    apply PV_RunJoin_CaptureRelation60.same_bind
    intro total
    apply PV_RunJoin_CaptureRelation60.same_bind
    intro zero
    apply PV_RunJoin_CaptureRelation60.same_bind
    intro balanced
    cases balanced with
    | false => exact PV_RunJoin_CaptureRelation60.error f _ _
    | true => exact PV_RunJoin_CaptureRelation60.tail f _ audit store
#print axioms complete
end R1Z.PV_RunJoin_CaptureAfterBuild60
