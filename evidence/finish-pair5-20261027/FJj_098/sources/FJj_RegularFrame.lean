import FJj_RegularTrace
import FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_RegularFrame
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
attribute [local irreducible] FIo_Native.weights.Weights.dense_point_pair
  FIo_Native.weights.Weights.tensor FIo_Native.weights.Weights.scalar_factor


theorem value [FIo_Native.Allocation] (w : FIo_Native.weights.Weights) (kind : Usize)
    (alpha : Slice NE) (f : Slice U8) (folds n : Usize) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (run : FIo_Native.weights.process_kind w kind alpha f folds n ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    ∀ j,kind.val≠j → FIp_ArrayValue.value after j=FIp_ArrayValue.value before j := by
  unfold FIo_Native.weights.process_kind at run
  repeat' first | (solve | cases run) | uncase_result | head_reduce run | split at run
  all_goals
    cases Result.ok.inj run
    intro j hj
    rw [FJc_ArrayUpdateValue.value before _ kind _ j (by assumption),if_neg hj]
#print axioms value
end AspisR1.FJj_RegularFrame
end
