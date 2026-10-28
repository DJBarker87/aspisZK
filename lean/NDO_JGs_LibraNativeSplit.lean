import NDO_JGs_LibraForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraNative
open Aeneas Aeneas.Std Result ControlFlow
theorem step0 : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {start:=0#usize,«end»:=2#usize} JGs_LibraEnd.initial=
    ok (.cont ({start:=1#usize,«end»:=2#usize},JGs_LibraEnd.middle)) := by
  exact JGs_LibraForward.source JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra
    {start:=0#usize,«end»:=2#usize} {start:=1#usize,«end»:=2#usize}
    JGs_LibraEnd.initial JGs_LibraEnd.middle 0#usize JGs_Libra.row0 JGs_LibraStage0.high
    JGs_Libra.q0_4 JGs_Libra.q0_16 JGs_LibraScale0.value
    0#usize 3#usize 2#usize 1#usize
    JGs_Libra.term0_0 JGs_Libra.term0_1 JGs_Libra.term0_2 JGs_Libra.term0_3
    JGs_Libra.sum0_2 JGs_Libra.sum0_3 JGs_Libra.sum0_4
    (JGo_TX2_Range.next 0#usize 2#usize 1#usize (by decide) (by decide))
    JGs_LibraStage0.powers JGs_LibraForward.scalar0 JGs_LibraStage0.term0 JGs_LibraStage0.term1 JGs_LibraStage0.term2 JGs_LibraStage0.term3 JGs_LibraStage0.totals JGs_LibraStage0.finish
#print axioms step0
theorem step1 : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {start:=1#usize,«end»:=2#usize} JGs_LibraEnd.middle=
    ok (.cont ({start:=2#usize,«end»:=2#usize},JGs_LibraEnd.value)) := by
  exact JGs_LibraForward.source JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra
    {start:=1#usize,«end»:=2#usize} {start:=2#usize,«end»:=2#usize}
    JGs_LibraEnd.middle JGs_LibraEnd.value 1#usize JGs_Libra.row1 JGs_LibraStage1.high
    JGs_Libra.q1_4 JGs_Libra.q1_16 JGs_LibraScale1.value
    0#usize 3#usize 2#usize 1#usize
    JGs_Libra.term1_0 JGs_Libra.term1_1 JGs_Libra.term1_2 JGs_Libra.term1_3
    JGs_Libra.sum1_2 JGs_Libra.sum1_3 JGs_Libra.sum1_4
    (JGo_TX2_Range.next 1#usize 2#usize 2#usize (by decide) (by decide))
    JGs_LibraStage1.powers JGs_LibraForward.scalar1 JGs_LibraStage1.term0 JGs_LibraStage1.term1 JGs_LibraStage1.term2 JGs_LibraStage1.term3 JGs_LibraStage1.totals JGs_LibraStage1.finish
#print axioms step1
end AspisR1.JGs_LibraNative
end
