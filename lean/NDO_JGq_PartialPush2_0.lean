import NDO_JGq_PartialData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push d2_0
    (FIo_Install.toE JGo_TX2_Message32.value32) JGq_Common.c0=ok (.Ok (),d2_1) := by
  have inc : Usize.wrapping_add d2_0.count 1#usize=1#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_0.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_0
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push d2_1
    (FIo_Install.toE JGo_TX2_Message32.value33) JGq_Common.c1=ok (.Ok (),d2_2) := by
  have inc : Usize.wrapping_add d2_1.count 1#usize=2#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_1.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push d2_2
    (FIo_Install.toE JGo_TX2_Message32.value34) JGq_Common.c2=ok (.Ok (),d2_3) := by
  have inc : Usize.wrapping_add d2_2.count 1#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_2.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_2
theorem push2_3 : FIo_Native.fast_pairing.EbyKDot.push d2_3
    (FIo_Install.toE JGo_TX2_Message32.value35) JGq_Common.c3=ok (.Ok (),d2_4) := by
  have inc : Usize.wrapping_add d2_3.count 1#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_3.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_3
end AspisR1.JGq_Partial
end
