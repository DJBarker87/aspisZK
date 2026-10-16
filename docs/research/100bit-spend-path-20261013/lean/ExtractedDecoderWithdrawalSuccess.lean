import ExtractedTerminalDecoderSuccess

/-! The actual decoder-nested terminal validator cannot return success without
its same-public ASWP encoder returning success. This is only prefix inversion;
no late/tree computation, account authentication or stage1 execution is assumed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1TerminalDecoder.WithdrawalSuccess
open pool_v1.pair_forest_terminal
open pool_v1.payment_relation

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem bool_guard_success {ε : Type} (m : Result Bool) (e : ε)
    (k : Result (core.result.Result Unit ε))
    (h : (do let b ← m; if b then ok (.Err e) else k) = ok (.Ok ())) :
    m = ok false ∧ k = ok (.Ok ()) := by
  obtain ⟨b, hb, hk⟩ := bind_success _ _ _ h
  cases b with
  | false => exact ⟨hb, by simpa only [Bool.false_eq_true, ↓reduceIte] using hk⟩
  | true => simp only [↓reduceIte] at hk; cases hk

theorem terminal_encoder_success
    (c : PoolV1PairForestTerminalCommonV1) (p : PoolV1WithdrawalPublicV1)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) =
      ok (.Ok ())) :
    ∃ pay : Array U8 216#usize,
      encode_pool_v1_withdrawal_public_v1 p = ok (.Ok pay) := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1 at h
  obtain ⟨common, hcommon, h⟩ := bind_success _ _ _ h
  have hc : common = c := by
    simpa only [PoolV1PairForestTerminalStatementV1.common, Result.ok.injEq] using hcommon.symm
  subst common
  obtain ⟨hm, h⟩ := bool_guard_success _ _ _ h
  obtain ⟨hc, h⟩ := bool_guard_success _ _ _ h
  obtain ⟨hs, h⟩ := bool_guard_success _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_success _ _ _ h
  have hi' : i = core.convert.num.FromUsizeU8.from c.output_lane := by
    simpa only [lift, Result.ok.injEq] using hi.symm
  subst i
  split at h
  · cases h
  · rename_i hlane
    dsimp only at h
    obtain ⟨r, hpay, h⟩ := bind_success _ _ _ h
    cases r with
    | Err e =>
        obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
        have hmap' : mapped = .Err (PoolV1PairForestTerminalFormatErrorV1.Payment e) := by
          simpa only [core.result.Result.map_err,
            validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,
            validate_pool_v1_pair_forest_terminal_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once,
            bind_tc_ok, Result.ok.injEq] using hmap.symm
        subst mapped
        obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
        have hcf' : cf = .Break (.Err (PoolV1PairForestTerminalFormatErrorV1.Payment e)) := by
          simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
        subst cf
        simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, bind_tc_ok] at h
        cases h
    | Ok pay => exact ⟨pay, hpay⟩

/-- Actual decoding supplies validation of the exact same returned withdrawal. -/
theorem decoder_encoder_success
    (bytes : Slice U8) (c : PoolV1PairForestTerminalCommonV1)
    (p : PoolV1WithdrawalPublicV1)
    (h : decode_pool_v1_pair_forest_terminal_statement_v1 bytes =
      ok (.Ok (.Withdrawal c p))) :
    ∃ pay : Array U8 216#usize,
      encode_pool_v1_withdrawal_public_v1 p = ok (.Ok pay) :=
  terminal_encoder_success c p
    (DecoderSuccess.decode_success_validated bytes (.Withdrawal c p) h)

#print axioms terminal_encoder_success
#print axioms decoder_encoder_success
end AspisR1TerminalDecoder.WithdrawalSuccess
