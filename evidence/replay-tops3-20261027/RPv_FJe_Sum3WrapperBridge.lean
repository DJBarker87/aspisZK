import RPv_FJe_Sum3IndexBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3WrapperBridge
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FIv_NativeArithmetic (qm)
open FIv_Map (map map_bind)
/-- Complete native prepared-three-products source correspondence on the
SAME ordered operands,including the actual channel-sum converter. -/
theorem same (a : Left) (b : Right) :
    map qm (FIq_Native.field.qm31_sum_products3_prepared a b)=
      AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared (left a) (right b) := by
  simp only [FIq_Native.field.qm31_sum_products3_prepared,
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared,
    map_bind,FJe_Sum3IndexBridge.same 3 ⟨0#usize,3#usize⟩ _ _ _ (by rfl),converter]
  all_goals rfl
#print axioms same
end AspisR1.FJe_Sum3WrapperBridge
end
