import NMS_R2RequestTransfer
import NMS_R2RequestWithdrawal
import NMS_R2R20Transition
import NMS_R2SliceArray
set_option autoImplicit false
namespace NMS_R2RequestSplitTotal
open Aeneas Aeneas.Std Result WP AspisR20Request
/-- The parent header composes separately checked payload arms. The former
whole-body heartbeat failure is not retried or given a larger limit. -/
@[step] theorem reference (bytes : Array U8 320#usize) :
 pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes
  ⦃ _ => True ⦄ := by
 rw [←NMS_R2RequestBranches.source]
 unfold NMS_R2RequestBranches.reference
   pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
   pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
 step*
 all_goals try scalar_tac
#print axioms reference
end NMS_R2RequestSplitTotal
