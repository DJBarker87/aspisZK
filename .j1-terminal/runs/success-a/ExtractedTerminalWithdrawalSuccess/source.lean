import ExtractedTerminalEquality

/-! Success inversion for the actual extracted terminal validator. The public
value is identical to the payment encoder's argument. These are the validator's
own checks; no account-owner, PDA, custody, or runtime-reachability claim is made. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1TerminalValidator.TerminalWithdrawalSuccess
open pool_v1.pair_forest_terminal pool_v1.payment_relation
open TerminalEquality

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- All direct guards, and the actual nested encoder successes, follow from
successful execution. No parser, chosen projection, or nested-success premise. -/
theorem terminal_withdrawal_success
    (c : PoolV1PairForestTerminalCommonV1) (p : PoolV1WithdrawalPublicV1)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) =
      ok (.Ok ())) :
    ∃ pay : Array U8 216#usize, ∃ late : Slice U8,
      encode_pool_v1_withdrawal_public_v1 p = ok (.Ok pay) ∧
      c.master_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.checkpoint_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.selected_lane_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.output_lane.val < 8 ∧
      p.pool = c.master_account ∧
      p.deployment_domain = c.lane_transition.live_snapshot.deployment_domain ∧
      c.lane_transition.live_snapshot.pool = c.master_account ∧
      p.anchor_sequence = c.checkpoint_sequence ∧
      p.anchor_root = c.historical_global_anchor ∧
      pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 p.nullifier =
        ok (.Ok c.output_lane) ∧
      pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
        c.lane_transition (Array.to_slice (Array.repeat 1520#usize 0#u8)) =
        ok (.Ok (), late) := by
  simp only [validate_pool_v1_pair_forest_terminal_statement_v1,
    PoolV1PairForestTerminalStatementV1.common, bind_tc_ok,
    array_eq_value core.cmp.PartialEqU8 u8_ne_spec, decide_eq_true_eq] at h
  split at h
  · cases h
  · rename_i hmaster
    split at h
    · cases h
    · rename_i hcheckpoint
      split at h
      · cases h
      · rename_i hselected
        simp only [lift, bind_tc_ok] at h
        split at h
        · cases h
        · rename_i hlane
          have hlane' : c.output_lane.val < 8 := by
            simp only [pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT,
              UScalar.le_equiv, core.convert.num.FromUsizeU8.from_val_eq,
              UScalar.ofNatCore_val_eq] at hlane
            omega
          obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
          cases r with
          | Err e =>
              simp only [core.result.Result.map_err,
                validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,
                validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once,
                bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at h
              cases h
          | Ok pay =>
              simp only [core.result.Result.map_err, bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch, statement_public_common,
                array_ne_value core.cmp.PartialEqU8 u8_ne_spec,
                array_ne_value aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m31_ne_spec,
                decide_eq_true_eq, bne_iff_ne] at h
              split at h
              · cases h
              · rename_i hpool
                split at h
                · cases h
                · rename_i hdeployment
                  split at h
                  · cases h
                  · rename_i hsnapshot
                    split at h
                    · cases h
                    · rename_i hsequence
                      split at h
                      · cases h
                      · rename_i hanchor
                        obtain ⟨r, hrLane, h⟩ := bind_success _ _ _ h
                        cases r with
                        | Err e =>
                            simp only [core.result.Result.map_err,
                              validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1,
                              validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once,
                              bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                              core.convert.FromSame.from] at h
                            cases h
                        | Ok lane =>
                            simp only [core.result.Result.map_err, bind_tc_ok,
                              core.result.Result.Insts.CoreOpsTry.branch, bne_iff_ne] at h
                            split at h
                            · cases h
                            · rename_i hlaneEq
                              have hlaneEq : lane = c.output_lane := by simpa using hlaneEq
                              subst lane
                              simp only [lift, Array.to_slice_mut, bind_tc_ok] at h
                              obtain ⟨⟨r, late⟩, hrLate, h⟩ := bind_success _ _ _ h
                              cases r with
                              | Err e =>
                                  simp only [core.result.Result.map_err,
                                    validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1,
                                    validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once,
                                    bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame.from] at h
                                  cases h
                              | Ok u =>
                                  cases u
                                  exact ⟨pay, late, hr, hmaster, hcheckpoint, hselected,
                                    hlane', by simpa using hpool, by simpa using hdeployment,
                                    by simpa using hsnapshot, by simpa using hsequence,
                                    by simpa using hanchor, hrLane, hrLate⟩

#print axioms terminal_withdrawal_success
end AspisR1TerminalValidator.TerminalWithdrawalSuccess
