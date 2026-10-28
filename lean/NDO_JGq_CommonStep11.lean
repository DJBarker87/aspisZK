import NDO_JGq_CommonData
import RPu_FJf_CommonIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] FIo_Native.weights.Weights.pair_loop1
/-- One actual common-coefficient write, on the installed weight object. -/
theorem step11 : FIo_Native.weights.Weights.pair_loop1.body w
    {start:=11#usize,«end»:=16#usize} a11=
    ok (.cont ({start:=12#usize,«end»:=16#usize},a12)) := by
  have low : (11#usize &&& 3#usize)=3#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.low];rfl)
  have high : Usize.wrapping_shr 11#usize 2#u32=2#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.high];rfl)
  unfold FIo_Native.weights.Weights.pair_loop1.body
  rw [JGo_TX2_Range.next 11#usize 16#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,low,high]
  with_unfolding_all rfl
#print axioms step11
end AspisR1.JGq_Common
end
