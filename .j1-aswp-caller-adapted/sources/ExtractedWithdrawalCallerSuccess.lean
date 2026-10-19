import AspisR1WithdrawalCaller.Funs

/-! Successful execution of the actual extracted ASWP encoder implies success
of its actual first validation call on the identical public structure. This
does not assert that an admitted verifier reaches the encoder, that the encoder
is total, or that its returned bytes have a separately specified serialization.
The retained validator-carrier transport is a subsequent, separate bridge. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1WithdrawalCaller.CallerSuccess
open pool_v1.payment_relation

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The actual `?` branch propagates the validator's exact error value. -/
theorem encoder_error_of_validator_error
    (p : PoolV1WithdrawalPublicV1) (e : PoolV1PaymentStatementFormatError)
    (h : validate_pool_v1_withdrawal_public_v1 p = ok (.Err e)) :
    encode_pool_v1_withdrawal_public_v1 p = ok (.Err e) := by
  simp only [encode_pool_v1_withdrawal_public_v1, h, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- No validator-success premise or chosen public projection is assumed. -/
theorem encoder_success_validator
    (p : PoolV1WithdrawalPublicV1) (bytes : Array U8 216#usize)
    (h : encode_pool_v1_withdrawal_public_v1 p = ok (.Ok bytes)) :
    validate_pool_v1_withdrawal_public_v1 p = ok (.Ok ()) := by
  unfold encode_pool_v1_withdrawal_public_v1 at h
  obtain ⟨r, hr, hk⟩ := bind_success _ _ _ h
  cases r with
  | Ok u => cases u; exact hr
  | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at hk
      cases hk

#print axioms pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
#print axioms pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
#print axioms encoder_error_of_validator_error
#print axioms encoder_success_validator
end AspisR1WithdrawalCaller.CallerSuccess
