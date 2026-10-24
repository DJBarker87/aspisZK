import S6NativeLateEncodeTotalV1
import S6StdByteArrayTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativePaymentValidatorTotal
open AspisR1TerminalDecoder
open pool_v1.payment_relation

@[step] theorem canonical_spec (digest : Array U32 8#usize) :
    digest_is_canonical digest ⦃ _ => True ⦄ := by
  unfold digest_is_canonical
  step*

@[step] theorem common_spec (common : CommonPublicV1) :
    validate_common common ⦃ _ => True ⦄ := by
  unfold validate_common pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY
    pool_v1.format.POOL_V1_TREE_DEPTH
  step*

@[step] theorem withdrawal_spec (public1 : PoolV1WithdrawalPublicV1) :
    validate_pool_v1_withdrawal_public_v1 public1 ⦃ _ => True ⦄ := by
  unfold validate_pool_v1_withdrawal_public_v1 withdrawal_common spend.VALUE_LIMIT
  step*

@[step] theorem transfer_spec (public1 : PoolV1PrivateTransferPublicV1) :
    validate_pool_v1_private_transfer_public_v1 public1 ⦃ _ => True ⦄ := by
  unfold validate_pool_v1_private_transfer_public_v1 transfer_common
  step*

/-- TOTAL complete payment validation, including malformed-input Rust errors. -/
theorem withdrawal_total (public1 : PoolV1WithdrawalPublicV1) :
    ∃ out,validate_pool_v1_withdrawal_public_v1 public1=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (withdrawal_spec public1)
  exact ⟨out,h⟩

theorem transfer_total (public1 : PoolV1PrivateTransferPublicV1) :
    ∃ out,validate_pool_v1_private_transfer_public_v1 public1=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (transfer_spec public1)
  exact ⟨out,h⟩

#print axioms canonical_spec
#print axioms common_spec
#print axioms withdrawal_total
#print axioms transfer_total
end AspisS6NativePaymentValidatorTotal
