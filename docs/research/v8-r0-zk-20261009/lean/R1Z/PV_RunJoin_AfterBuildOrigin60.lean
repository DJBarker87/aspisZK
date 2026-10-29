import R1Z.PV_RunJoin_BuildOrigin60
import R1Z.PV_RunJoin_NativeAfterBuild55
import R1Z.ProverRwOuterMapErr
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AfterBuildOrigin60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ResultPost41
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) {T : Type}
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (audit : prover.MaskedFixtureAudit) (store : T)
    (r14 : core.result.Result (host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) r1_wire.Error) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    Post (fun pair => match pair.1 with
      | .Err _ => True
      | .Ok (p,_) => r14=.Ok p.sem ∧ p.backend=backend ∧ p.hash=hash ∧ p.public1=public1 ∧ p.variant=variant)
      (PV_RunJoin_NativeAfterBuild55.run capture public1 variant hash backend reserved context audit store r14) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  unfold PV_RunJoin_NativeAfterBuild55.run
  cases r14 with
  | Err e =>
    simp only [ProverRwOuterMapErr.installed,ProverRwOuterMapErr.map_err,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro mapped
    trivial
  | Ok sem =>
    simp only [ProverRwOuterMapErr.installed,ProverRwOuterMapErr.map_err,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    apply PV_RunJoin_ResultPost41.bind
    intro column
    apply PV_RunJoin_ResultPost41.bind
    intro total
    apply PV_RunJoin_ResultPost41.bind
    intro zero
    apply PV_RunJoin_ResultPost41.bind
    intro balanced
    cases balanced with
    | false => trivial
    | true => exact ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms complete
end R1Z.PV_RunJoin_AfterBuildOrigin60
