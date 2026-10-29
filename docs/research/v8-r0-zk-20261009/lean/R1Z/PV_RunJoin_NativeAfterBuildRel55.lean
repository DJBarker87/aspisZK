import R1Z.PV_RunJoin_NativeAfterBuild55
import R1Z.PV_RunJoin_NativeResult55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAfterBuildRel55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_ResultRelation55 PV_RunJoin_NativeResult55
variable [ExternalTypes] [ExternalFuns]
theorem complete {A B T : Type} (R : A → B → Prop)
    (f : Phase → Result (core.result.Result A verifier.Error))
    (g : Phase → Result (core.result.Result B verifier.Error))
    (step : ∀ p,Rel (CoreRel R) (f p) (g p))
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (r14 : core.result.Result (host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) r1_wire.Error) :
    Rel (Output R)
      (PV_RunJoin_NativeAfterBuild55.run f public1 variant hash backend reserved context audit store r14)
      (PV_RunJoin_NativeAfterBuild55.run g public1 variant hash backend reserved context audit store r14) := by
  unfold PV_RunJoin_NativeAfterBuild55.run
  apply PV_RunJoin_ResultRelation55.same_bind
  intro status
  cases status with
  | Err e => exact PV_RunJoin_NativeResult55.error R _ _
  | Ok sem =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro column
    apply PV_RunJoin_ResultRelation55.same_bind
    intro total
    apply PV_RunJoin_ResultRelation55.same_bind
    intro zero
    apply PV_RunJoin_ResultRelation55.same_bind
    intro balanced
    cases balanced with
    | false => exact PV_RunJoin_NativeResult55.error R _ _
    | true => exact PV_RunJoin_NativeResult55.tail R _ _ audit store (step _)
#print axioms complete
end R1Z.PV_RunJoin_NativeAfterBuildRel55
