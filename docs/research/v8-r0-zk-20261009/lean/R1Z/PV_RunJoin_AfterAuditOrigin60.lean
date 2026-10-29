import R1Z.PV_RunJoin_AfterBuildOrigin60
import R1Z.PV_RunJoin_NativeAfterAudit55
import R1Z.PV_RunJoin_FromElemLength60
import R1Z.PV_RunJoin_PostEquation60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AfterAuditOrigin60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualProvenance60 (capture)
open PV_RunJoin_ResultPost41 PV_RunJoin_BuildOrigin60
variable [ExternalTypes]
theorem complete (ops : ExternalFuns) {T0 : Type}
    (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (hash : aspis_core.digest.LegacyHashFn)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g_ h1_padding : Array aspis_core.field.QM31 1024#usize)
    (audit : prover.MaskedFixtureAudit) (store : T0) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok (p,_) => Origin p)
      (PV_RunJoin_NativeAfterAudit55.run capture aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
        public1 compiled .S2 hash reserved context noised maskOnly d g_ h1_padding audit store) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  unfold PV_RunJoin_NativeAfterAudit55.run
  apply PV_RunJoin_ResultPost41.bind
  intro tag1
  apply PV_RunJoin_ResultPost41.bind
  intro saltResult1
  cases saltResult1 with
  | Err e => trivial
  | Ok salts1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro tag2
    apply PV_RunJoin_ResultPost41.bind
    intro saltResult2
    cases saltResult2 with
    | Err e => trivial
    | Ok salts2 =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro domainResult
      apply PV_RunJoin_ResultPost41.bind
      intro mappedDomain
      cases mappedDomain with
      | Err e => trivial
      | Ok domain =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro zero
        apply PV_RunJoin_PostEquation60.bind
        intro messages hmessages
        have hlen : messages.length=29 := PV_RunJoin_FromElemLength60.complete _ _ 29#usize _ hmessages
        apply PV_RunJoin_PostEquation60.bind
        intro pair hbuild
        rcases pair with ⟨result,backend⟩
        dsimp only [Aeneas.Std.uncurry]
        have finish := PV_RunJoin_AfterBuildOrigin60.complete ops public1 .S2 hash backend reserved context audit store result
        cases hf : PV_RunJoin_NativeAfterBuild55.run capture public1 .S2 hash backend reserved context audit store result with
        | fail e => trivial
        | div => trivial
        | ok out =>
          rw [hf] at finish
          rcases out with ⟨status,next⟩
          cases status with
          | Err e => trivial
          | Ok published =>
            rcases published with ⟨p,finishedAudit⟩
            obtain ⟨hsem,hbackend,hhash,hpublic,hvariant⟩ := finish
            refine ⟨hvariant,compiled,noised,maskOnly,d,g_,h1_padding,
              {hash:=hash,variant:=.S2,domain:=domain,messages:=messages,c1:=none,c2:=none,
                c1_salts:=some salts1,c2_salts:=some salts2},hlen,?_⟩
            rw [hpublic,hhash,hbackend]
            rw [hsem] at hbuild
            exact hbuild

#print axioms complete
end R1Z.PV_RunJoin_AfterAuditOrigin60
