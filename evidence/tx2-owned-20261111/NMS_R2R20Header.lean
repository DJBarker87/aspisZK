import NFY_Part060
set_option autoImplicit false
namespace NMS_R2R20Header
open Aeneas Aeneas.Std Result WP AspisR20Request
/-- Header checks on arbitrary symbolic216-byte payment images. -/
@[step] theorem total (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
 (kind : pool_v1.historical_anchor.PoolV1TransitionKind) :
 pool_v1.payment_relation.require_header bytes magic kind ⦃ _ => True ⦄ := by
 unfold pool_v1.payment_relation.require_header
   pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION
   pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
 step*
 all_goals exact AspisS6StdByteSlice.eq_spec _ _
#print axioms total
end NMS_R2R20Header
