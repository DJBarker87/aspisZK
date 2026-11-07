import NMS_R2R20Header
import NMS_R2R20Validators
import NMS_R2R20ActualMaps
set_option autoImplicit false
namespace NMS_R2R20Common
open Aeneas Aeneas.Std Result WP AspisR20Request
/-- Arbitrary payment image; static read windows are source inputs, not
successful codec assumptions. -/
@[step] theorem total (bytes : Array U8 216#usize) :
 pool_v1.payment_relation.decode_common bytes ⦃ _ => True ⦄ := by
 unfold pool_v1.payment_relation.decode_common
   pool_v1.payment_relation.ASSET_ID_OFFSET pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
   pool_v1.payment_relation.POOL_OFFSET pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET
   pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET pool_v1.payment_relation.ANCHOR_ROOT_OFFSET
   pool_v1.payment_relation.NULLIFIER_OFFSET
 step*
 all_goals (cases r <;> simp_all)
 all_goals step*
 all_goals (cases r1 <;> simp_all)
 all_goals step*
 all_goals (cases r2 <;> simp_all)
 all_goals step*
 all_goals (cases r3 <;> simp_all)
 all_goals step*
 all_goals (cases r4 <;> simp_all)
 all_goals step*
 all_goals (cases r7 <;> simp_all)
 all_goals step*
 all_goals try scalar_tac
#print axioms total
end NMS_R2R20Common
