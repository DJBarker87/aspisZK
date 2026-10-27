import FJg_ScalarValue
import SAG_QuarterBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_QuarterBase
open AspisR1CurrentWide.Proof

theorem literal : decodeM FIo_Native.weights.QUARTER=(536870912 : ExactM) := by
  unfold FIo_Native.weights.QUARTER
  rfl

theorem value : (4 : ExactM)*decodeM FIo_Native.weights.QUARTER=1 := by
  rw [literal]
  exact SAG_QuarterBase.four_times
#print axioms literal
#print axioms value
end AspisR1.FJg_QuarterBase
end
