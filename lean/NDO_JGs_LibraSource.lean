import NDO_JGs_LibraNativeSplit
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraSource
open Aeneas Aeneas.Std Result ControlFlow
abbrev S := core.ops.range.Range Usize × Array FIo_Install.NE 4#usize
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=2#usize},JGs_LibraEnd.initial)
  | 1 => ({start:=1#usize,«end»:=2#usize},JGs_LibraEnd.middle)
  | _ => ({start:=2#usize,«end»:=2#usize},JGs_LibraEnd.value)
theorem source : FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra=ok JGs_LibraEnd.value := by
  unfold FIo_Native.weights.factored_s2_libra_weights FIo_Native.weights.factored_s2_libra_weights_loop
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
      (FIo_Install.toWeights JGo_TX2_WeightData.value).extra t.1 t.2) states 2 JGs_LibraEnd.value
  · intro i hi
    interval_cases i
    · exact JGs_LibraNative.step0
    · exact JGs_LibraNative.step1
  · unfold FIo_Native.weights.factored_s2_libra_weights_loop.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGs_LibraSource
end
