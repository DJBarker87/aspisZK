import JGq_CommonData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] FIo_Native.weights.Weights.pair_loop1
/-- One actual common-coefficient write, on the installed weight object. -/
theorem step0 : FIo_Native.weights.Weights.pair_loop1.body w
    {start:=0#usize,«end»:=16#usize} a0=
    ok (.cont ({start:=1#usize,«end»:=16#usize},a1)) := by
  unfold FIo_Native.weights.Weights.pair_loop1.body
  rw [JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide),bind_tc_ok]
  with_unfolding_all rfl
#print axioms step0
end AspisR1.JGq_Common
end
