import NDO_JFn_DotsSlot
import RPz7_FIp_DotsAdapter
import FIp_CircleQuery
import RPz7_FIp_Equality
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_DotsBinding
open Aeneas Aeneas.Std Result

/-- The actual installed query children; no successful-result callback is used. -/
def ops (seed : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
  JFn_ArrayBuilder.ops {seed with op20 := FIp_DotsAdapter.dots, op17 := FIp_CircleQuery.circle,widePartialEq := FIp_Equality.dictionary}

theorem dots (seed : Port3_NativeQueryBody.Ops) :
    (ops seed).op20=FIp_DotsAdapter.dots := JFn_DotsSlot.retained _

theorem circle (seed : Port3_NativeQueryBody.Ops) :
    (ops seed).op17=FIp_CircleQuery.circle := by
  unfold ops JFn_ArrayBuilder.ops Port4C_RowStd.install Port3_NativeRowFrame.install
    Port4C_QueryStd.install Port5Q1_QueryPorts.install SAQ_Decoder.install
    SAQ_LineQuery.install SAQ_QuerySource.install SAQ_Arithmetic.install SAQ_Query.install
  rfl

#print axioms dots
#print axioms circle
end AspisR1.JFr_TX2_DotsBinding
end
