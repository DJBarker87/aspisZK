import S6SourcePaymentCommonEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentEncodeTotal
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

@[step] theorem withdrawal_write_spec (public1 : PoolV1WithdrawalPublicV1) :
    encode_pool_v1_withdrawal_public_v1 public1 ⦃ _ => True ⦄ := by
  unfold encode_pool_v1_withdrawal_public_v1 withdrawal_common
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

@[step] theorem transfer_write_spec (public1 : PoolV1PrivateTransferPublicV1) :
    encode_pool_v1_private_transfer_public_v1 public1 ⦃ _ => True ⦄ := by
  unfold encode_pool_v1_private_transfer_public_v1 transfer_common
    FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

/-- TOTAL actual source payment encoders; errors are ordinary Rust values. -/
theorem withdrawal_write_total (public1 : PoolV1WithdrawalPublicV1) :
    ∃ out,encode_pool_v1_withdrawal_public_v1 public1=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (withdrawal_write_spec public1)
  exact ⟨out,h⟩

theorem transfer_write_total (public1 : PoolV1PrivateTransferPublicV1) :
    ∃ out,encode_pool_v1_private_transfer_public_v1 public1=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (transfer_write_spec public1)
  exact ⟨out,h⟩

#print axioms withdrawal_write_total
#print axioms transfer_write_total
end AspisS6SourceCodec.PaymentEncodeTotal
