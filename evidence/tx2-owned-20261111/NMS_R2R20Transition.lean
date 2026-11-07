import NFY_Part060
set_option autoImplicit false
namespace NMS_R2R20Transition
open Aeneas Aeneas.Std Result WP AspisR20Request
/-- Every transition tag, including rejection, returns without outer fail/div. -/
@[step] theorem total (tag : U8) :
 pool_v1.pair_forest_terminal.transition_kind tag ⦃ _ => True ⦄ := by
 unfold pool_v1.pair_forest_terminal.transition_kind
 step*
#print axioms total
end NMS_R2R20Transition
