import RPv_FJk_ActiveValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_ActiveValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
/-- The fixed zero seed and zero start of the actual active wrapper. -/
theorem value (s : Selectors) (out : field.QM31)
    (hh : canonical s.high) (hl : canonical s.low)
    (run : Selectors.active s=ok out) :
    Canon out ∧ decode out=R0P.copyActiveLiteral (FIw_CopyEndpoint.modelSelectors s) := by
  have got := FJk_ActiveValue.loop 64 0#usize s field.QM31.ZERO out rfl hh hl
    FIv_NativeValue.zero.1 run
  refine ⟨got.1,?_⟩
  rw [got.2,FIv_NativeValue.zero.2]
  rfl
#print axioms value
end AspisR1.FJn_ActiveValue
end
