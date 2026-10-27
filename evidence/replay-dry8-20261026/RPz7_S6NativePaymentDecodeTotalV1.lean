import RPz7_S6NativePaymentHeaderTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativePaymentDecode
open AspisR1TerminalDecoder
open pool_v1.payment_relation

/-- TOTAL complete transfer decoder on arbitrary slices, including length,
header, noncanonical word/digest and validator rejection paths. -/
@[step] theorem transfer_spec (bytes : Slice U8) :
    decode_pool_v1_private_transfer_public_v1 bytes ⦃ _ => True ⦄ := by
  unfold decode_pool_v1_private_transfer_public_v1
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r7 <;> simp_all)
  all_goals step*

/-- TOTAL complete withdrawal decoder on arbitrary slices, with no successful
child, canonical-input or fixed-length assumption. -/
@[step] theorem withdrawal_spec (bytes : Slice U8) :
    decode_pool_v1_withdrawal_public_v1 bytes ⦃ _ => True ⦄ := by
  unfold decode_pool_v1_withdrawal_public_v1
    AMOUNT_OR_RESERVED_OFFSET FIRST_OUTPUT_OR_DESTINATION_OFFSET SECOND_OUTPUT_OFFSET
  step*
  all_goals (cases r4 <;> simp_all)
  all_goals step*
  all_goals (cases r5 <;> simp_all)
  all_goals step*
  all_goals (cases r6 <;> simp_all)
  all_goals step*

theorem transfer_total (bytes : Slice U8) :
    ∃ result, decode_pool_v1_private_transfer_public_v1 bytes=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (transfer_spec bytes)
  exact ⟨result,h⟩

theorem withdrawal_total (bytes : Slice U8) :
    ∃ result, decode_pool_v1_withdrawal_public_v1 bytes=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (withdrawal_spec bytes)
  exact ⟨result,h⟩

#print axioms transfer_total
#print axioms withdrawal_total
end AspisS6NativePaymentDecode
