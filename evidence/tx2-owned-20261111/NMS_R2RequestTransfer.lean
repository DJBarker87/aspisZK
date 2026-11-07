import NMS_R2RequestBranches
set_option autoImplicit false
namespace NMS_R2RequestTransfer
open Aeneas Aeneas.Std Result WP AspisR20Request
@[step] theorem total (bytes : Array U8 320#usize) :
 NMS_R2RequestBranches.transfer bytes ⦃ _ => True ⦄ := by
 unfold NMS_R2RequestBranches.transfer
   pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
   pool_v1.pair_forest_terminal.REQUEST_PROFILE_OFFSET
   pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET
   pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET
 step*
 all_goals try scalar_tac
#print axioms total
end NMS_R2RequestTransfer
