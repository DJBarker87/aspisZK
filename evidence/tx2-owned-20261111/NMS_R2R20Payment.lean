import NMS_R2R20Common
set_option autoImplicit false
namespace NMS_R2R20Payment
open Aeneas Aeneas.Std Result WP AspisR20Request
@[step] theorem transfer (bytes : Slice U8) :
 pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1 bytes ⦃ _ => True ⦄ := by
 unfold pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
   pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
   pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
   pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
   core.cmp.PartialEq.ne.trait_default AspisR20Request.Slice.Insts.CoreCmpPartialEqSlice
 step*
 all_goals try exact AspisS6StdByteSlice.eq_spec _ _
 all_goals (cases r4 <;> simp_all)
 all_goals step*
 all_goals (cases r7 <;> simp_all)
 all_goals step*
@[step] theorem withdrawal (bytes : Slice U8) :
 pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes ⦃ _ => True ⦄ := by
 unfold pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1
   pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
   pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
   pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
 step*
 all_goals (cases r4 <;> simp_all)
 all_goals step*
 all_goals (cases r5 <;> simp_all)
 all_goals step*
 all_goals (cases r6 <;> simp_all)
 all_goals step*
#print axioms transfer
#print axioms withdrawal
end NMS_R2R20Payment
