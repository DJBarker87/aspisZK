import RPt_JFn_ArrayBuilder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_DotsSlot
open Aeneas Aeneas.Std Result

/-- The exact retained dot callback; each dictionary layer is unfolded
symbolically to avoid whole-record definitional normalization. -/
theorem retained (seed : Port3_NativeQueryBody.Ops) : (JFn_ArrayBuilder.ops seed).op20=seed.op20 := by
  unfold JFn_ArrayBuilder.ops Port4C_RowStd.install Port3_NativeRowFrame.install
    Port4C_QueryStd.install Port5Q1_QueryPorts.install SAQ_Decoder.install
    SAQ_LineQuery.install SAQ_QuerySource.install SAQ_Arithmetic.install SAQ_Query.install
  rfl

#print axioms retained
end AspisR1.JFn_DotsSlot
end
