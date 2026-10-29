import R1Z.PV_RunJoin_NativeAuditContext55
import R1Z.PV_RunJoin_NativeAfterAuditRel55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeAuditRel55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeControl55
open PV_RunJoin_ResultRelation55 PV_RunJoin_NativeResult55
variable [ExternalTypes] [ExternalFuns]
theorem complete {A B : Type} (R : A → B → Prop)
    (f : Phase → Result (core.result.Result A verifier.Error))
    (g : Phase → Result (core.result.Result B verifier.Error))
    (step : ∀ p,Rel (CoreRel R) (f p) (g p))
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
    Rel (Output R)
      (PV_RunJoin_NativeAuditContext55.run f aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store)
      (PV_RunJoin_NativeAuditContext55.run g aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store) := by
  unfold PV_RunJoin_NativeAuditContext55.run
  apply PV_RunJoin_ResultRelation55.same_bind
  intro reservation
  dsimp only [Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultRelation55.same_bind
  intro maskStatus
  cases maskStatus with
  | Err e => exact PV_RunJoin_NativeResult55.error R _ _
  | Ok maskPair =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro cloned
    apply PV_RunJoin_ResultRelation55.same_bind
    intro applied
    dsimp only [Aeneas.Std.uncurry]
    apply PV_RunJoin_ResultRelation55.same_bind
    intro appliedStatus
    cases appliedStatus with
    | Err e => exact PV_RunJoin_NativeResult55.error R _ _
    | Ok masks =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultRelation55.same_bind
      intro activeResult
      apply PV_RunJoin_ResultRelation55.same_bind
      intro activeStatus
      cases activeStatus with
      | Err e => exact PV_RunJoin_NativeResult55.error R _ _
      | Ok active =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultRelation55.same_bind
        intro dResult
        apply PV_RunJoin_ResultRelation55.same_bind
        intro dStatus
        cases dStatus with
        | Err e => exact PV_RunJoin_NativeResult55.error R _ _
        | Ok dvec =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply PV_RunJoin_ResultRelation55.same_bind
          intro arrayResult
          apply PV_RunJoin_ResultRelation55.same_bind
          intro arrayStatus
          cases arrayStatus with
          | Err e => exact PV_RunJoin_NativeResult55.error R _ _
          | Ok d =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            by_cases glen : (alloc.vec.Vec.len masks.g != 1024#usize)=true
            · simp only [if_pos glen]
              exact PV_RunJoin_NativeResult55.error R _ _
            · simp only [if_neg glen]
              by_cases plen : (alloc.vec.Vec.len masks.h1_padding != 1024#usize)=true
              · simp only [if_pos plen]
                exact PV_RunJoin_NativeResult55.error R _ _
              · simp only [if_neg plen]
                apply PV_RunJoin_ResultRelation55.same_bind
                intro gcol
                apply PV_RunJoin_ResultRelation55.same_bind
                intro padding
                simp only [lift,bind_tc_ok]
                apply PV_RunJoin_ResultRelation55.same_bind
                intro audit
                by_cases c1count : (audit.c1_columns_inactive_balanced != 16#usize)=true
                · simp only [if_pos c1count]
                  exact PV_RunJoin_NativeResult55.error R _ _
                · simp only [if_neg c1count]
                  by_cases maskcount : (audit.mask_only_columns_inactive_balanced != 10#usize)=true
                  · simp only [if_pos maskcount]
                    exact PV_RunJoin_NativeResult55.error R _ _
                  · simp only [if_neg maskcount]
                    by_cases d_inactive_balanced : ¬(audit.d_inactive_balanced=true)
                    · simp only [if_neg d_inactive_balanced]
                      exact PV_RunJoin_NativeResult55.error R _ _
                    · have d_inactive_balancedgood : audit.d_inactive_balanced=true := Classical.not_not.mp d_inactive_balanced
                      simp only [if_pos d_inactive_balancedgood]
                      by_cases g_inactive_balanced : ¬(audit.g_inactive_balanced=true)
                      · simp only [if_neg g_inactive_balanced]
                        exact PV_RunJoin_NativeResult55.error R _ _
                      · have g_inactive_balancedgood : audit.g_inactive_balanced=true := Classical.not_not.mp g_inactive_balanced
                        simp only [if_pos g_inactive_balancedgood]
                        by_cases h1_padding_inactive_balanced : ¬(audit.h1_padding_inactive_balanced=true)
                        · simp only [if_neg h1_padding_inactive_balanced]
                          exact PV_RunJoin_NativeResult55.error R _ _
                        · have h1_padding_inactive_balancedgood : audit.h1_padding_inactive_balanced=true := Classical.not_not.mp h1_padding_inactive_balanced
                          simp only [if_pos h1_padding_inactive_balancedgood]
                          apply PV_RunJoin_NativeAfterAuditRel55.complete R f g step
#print axioms complete
end R1Z.PV_RunJoin_NativeAuditRel55
