import R1Z.PV_RunJoin_NativePhaseSource55
import R1Z.PV_RunJoin_ResultBindEq55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeControlSource55
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
theorem complete
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
    prover.prove_masked_with_attempt aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      public1 compiled variant hash context binding attempt nonce_store=
    PV_RunJoin_NativeControl55.run PV_RunJoin_NativeControl55.source
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst
      public1 compiled variant hash context binding attempt nonce_store := by
  unfold prover.prove_masked_with_attempt PV_RunJoin_NativeControl55.run
  apply PV_RunJoin_ResultBindEq55.complete
  intro reservation
  dsimp only [Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultBindEq55.complete
  intro maskStatus
  cases maskStatus with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  | Ok maskPair =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultBindEq55.complete
    intro cloned
    apply PV_RunJoin_ResultBindEq55.complete
    intro applied
    dsimp only [Aeneas.Std.uncurry]
    apply PV_RunJoin_ResultBindEq55.complete
    intro appliedStatus
    cases appliedStatus with
    | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    | Ok masks =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultBindEq55.complete
      intro activeResult
      apply PV_RunJoin_ResultBindEq55.complete
      intro activeStatus
      cases activeStatus with
      | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      | Ok active =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultBindEq55.complete
        intro dResult
        apply PV_RunJoin_ResultBindEq55.complete
        intro dStatus
        cases dStatus with
        | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        | Ok dvec =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply PV_RunJoin_ResultBindEq55.complete
          intro arrayResult
          apply PV_RunJoin_ResultBindEq55.complete
          intro arrayStatus
          cases arrayStatus with
          | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          | Ok d =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            by_cases glen : (alloc.vec.Vec.len masks.g != 1024#usize)=true
            · simp only [if_pos glen]
              rfl
            · simp only [if_neg glen]
              by_cases plen : (alloc.vec.Vec.len masks.h1_padding != 1024#usize)=true
              · simp only [if_pos plen]
                rfl
              · simp only [if_neg plen]
                apply PV_RunJoin_ResultBindEq55.complete
                intro gcol
                apply PV_RunJoin_ResultBindEq55.complete
                intro padding
                simp only [lift,bind_tc_ok]
                apply PV_RunJoin_ResultBindEq55.complete
                intro audit
                by_cases c1count : (audit.c1_columns_inactive_balanced != 16#usize)=true
                · simp only [if_pos c1count]
                  rfl
                · simp only [if_neg c1count]
                  by_cases maskcount : (audit.mask_only_columns_inactive_balanced != 10#usize)=true
                  · simp only [if_pos maskcount]
                    rfl
                  · simp only [if_neg maskcount]
                    by_cases d_inactive_balanced : ¬(audit.d_inactive_balanced=true)
                    · simp only [if_neg d_inactive_balanced]
                      rfl
                    · have d_inactive_balancedgood : audit.d_inactive_balanced=true := Classical.not_not.mp d_inactive_balanced
                      simp only [if_pos d_inactive_balancedgood]
                      by_cases g_inactive_balanced : ¬(audit.g_inactive_balanced=true)
                      · simp only [if_neg g_inactive_balanced]
                        rfl
                      · have g_inactive_balancedgood : audit.g_inactive_balanced=true := Classical.not_not.mp g_inactive_balanced
                        simp only [if_pos g_inactive_balancedgood]
                        by_cases h1_padding_inactive_balanced : ¬(audit.h1_padding_inactive_balanced=true)
                        · simp only [if_neg h1_padding_inactive_balanced]
                          rfl
                        · have h1_padding_inactive_balancedgood : audit.h1_padding_inactive_balanced=true := Classical.not_not.mp h1_padding_inactive_balanced
                          simp only [if_pos h1_padding_inactive_balancedgood]
                          apply PV_RunJoin_ResultBindEq55.complete
                          intro tag1
                          apply PV_RunJoin_ResultBindEq55.complete
                          intro saltResult1
                          cases saltResult1 with
                          | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                          | Ok salts1 =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                            apply PV_RunJoin_ResultBindEq55.complete
                            intro tag2
                            apply PV_RunJoin_ResultBindEq55.complete
                            intro saltResult2
                            cases saltResult2 with
                            | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                            | Ok salts2 =>
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                              apply PV_RunJoin_ResultBindEq55.complete
                              intro domainResult
                              apply PV_RunJoin_ResultBindEq55.complete
                              intro mappedDomain
                              cases mappedDomain with
                              | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                              | Ok domain =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                apply PV_RunJoin_ResultBindEq55.complete
                                intro zero
                                apply PV_RunJoin_ResultBindEq55.complete
                                intro messages
                                apply PV_RunJoin_ResultBindEq55.complete
                                intro builtPair
                                dsimp only [Aeneas.Std.uncurry]
                                apply PV_RunJoin_ResultBindEq55.complete
                                intro builtStatus
                                cases builtStatus with
                                | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                | Ok sem =>
                                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                  apply PV_RunJoin_ResultBindEq55.complete
                                  intro column
                                  apply PV_RunJoin_ResultBindEq55.complete
                                  intro total
                                  apply PV_RunJoin_ResultBindEq55.complete
                                  intro zeroQ
                                  apply PV_RunJoin_ResultBindEq55.complete
                                  intro balanced
                                  cases balanced with
                                  | false => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
                                  | true =>
                                    rw [PV_RunJoin_NativePhaseSource55.complete]
                                    all_goals rfl

#print axioms complete
end R1Z.PV_RunJoin_NativeControlSource55
