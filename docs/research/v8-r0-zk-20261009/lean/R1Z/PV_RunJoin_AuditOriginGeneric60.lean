import R1Z.PV_RunJoin_NativeAuditContext55
import R1Z.PV_RunJoin_AfterAuditOriginGeneric60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AuditOriginGeneric60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_ResultPost41 PV_RunJoin_BuildOrigin60
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes]
theorem complete (ops : ExternalFuns) (law : @ExternalFuns.op12 _ ops=@ProverRwOuterMapErr.map_err)
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
    letI : ExternalFuns := ops
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok (p,_) => Origin p)
      (PV_RunJoin_NativeAuditContext55.run capture aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled .S2 hash context binding attempt nonce_store) := by
  letI : ExternalFuns := ops
  unfold PV_RunJoin_NativeAuditContext55.run
  apply PV_RunJoin_ResultPost41.bind
  intro reservation
  dsimp only [Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultPost41.bind
  intro maskStatus
  cases maskStatus with
  | Err e => trivial
  | Ok maskPair =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro cloned
    apply PV_RunJoin_ResultPost41.bind
    intro applied
    dsimp only [Aeneas.Std.uncurry]
    apply PV_RunJoin_ResultPost41.bind
    intro appliedStatus
    cases appliedStatus with
    | Err e => trivial
    | Ok masks =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro activeResult
      apply PV_RunJoin_ResultPost41.bind
      intro activeStatus
      cases activeStatus with
      | Err e => trivial
      | Ok active =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro dResult
        apply PV_RunJoin_ResultPost41.bind
        intro dStatus
        cases dStatus with
        | Err e => trivial
        | Ok dvec =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply PV_RunJoin_ResultPost41.bind
          intro arrayResult
          apply PV_RunJoin_ResultPost41.bind
          intro arrayStatus
          cases arrayStatus with
          | Err e => trivial
          | Ok d =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            by_cases glen : (alloc.vec.Vec.len masks.g != 1024#usize)=true
            · simp only [if_pos glen]
              trivial
            · simp only [if_neg glen]
              by_cases plen : (alloc.vec.Vec.len masks.h1_padding != 1024#usize)=true
              · simp only [if_pos plen]
                trivial
              · simp only [if_neg plen]
                apply PV_RunJoin_ResultPost41.bind
                intro gcol
                apply PV_RunJoin_ResultPost41.bind
                intro padding
                simp only [lift,bind_tc_ok]
                apply PV_RunJoin_ResultPost41.bind
                intro audit
                by_cases c1count : (audit.c1_columns_inactive_balanced != 16#usize)=true
                · simp only [if_pos c1count]
                  trivial
                · simp only [if_neg c1count]
                  by_cases maskcount : (audit.mask_only_columns_inactive_balanced != 10#usize)=true
                  · simp only [if_pos maskcount]
                    trivial
                  · simp only [if_neg maskcount]
                    by_cases d_inactive_balanced : ¬(audit.d_inactive_balanced=true)
                    · simp only [if_neg d_inactive_balanced]
                      trivial
                    · have d_inactive_balancedgood : audit.d_inactive_balanced=true := Classical.not_not.mp d_inactive_balanced
                      simp only [if_pos d_inactive_balancedgood]
                      by_cases g_inactive_balanced : ¬(audit.g_inactive_balanced=true)
                      · simp only [if_neg g_inactive_balanced]
                        trivial
                      · have g_inactive_balancedgood : audit.g_inactive_balanced=true := Classical.not_not.mp g_inactive_balanced
                        simp only [if_pos g_inactive_balancedgood]
                        by_cases h1_padding_inactive_balanced : ¬(audit.h1_padding_inactive_balanced=true)
                        · simp only [if_neg h1_padding_inactive_balanced]
                          trivial
                        · have h1_padding_inactive_balancedgood : audit.h1_padding_inactive_balanced=true := Classical.not_not.mp h1_padding_inactive_balanced
                          simp only [if_pos h1_padding_inactive_balancedgood]
                          apply PV_RunJoin_AfterAuditOriginGeneric60.complete ops
#print axioms complete
end R1Z.PV_RunJoin_AuditOriginGeneric60
