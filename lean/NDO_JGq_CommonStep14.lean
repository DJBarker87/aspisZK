import NDO_JGq_CommonData
import RPu_FJf_CommonIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] FIo_Native.weights.Weights.pair_loop1
/-- One actual common-coefficient write, on the installed weight object. -/
theorem step14 : FIo_Native.weights.Weights.pair_loop1.body w
    {start:=14#usize,«end»:=16#usize} a14=
    ok (.cont ({start:=15#usize,«end»:=16#usize},a15)) := by
  have low : (14#usize &&& 3#usize)=2#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.low];rfl)
  have high : Usize.wrapping_shr 14#usize 2#u32=3#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.high];rfl)
  unfold FIo_Native.weights.Weights.pair_loop1.body
  rw [JGo_TX2_Range.next 14#usize 16#usize 15#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,low,high]
  with_unfolding_all rfl
#print axioms step14
end AspisR1.JGq_Common
end
