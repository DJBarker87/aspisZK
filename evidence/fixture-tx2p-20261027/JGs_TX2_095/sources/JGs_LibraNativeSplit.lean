import JGs_LibraStage0
import JGs_LibraStage1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraNative
open Aeneas Aeneas.Std Result ControlFlow
theorem step0 : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {start:=0#usize,«end»:=2#usize} JGs_LibraEnd.initial=
    ok (.cont ({start:=1#usize,«end»:=2#usize},JGs_LibraEnd.middle)) := by
  rw [JGs_LibraProgram.source]
  unfold JGs_LibraProgram.body
  rw [JGo_TX2_Range.next 0#usize 2#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,JGs_LibraStage0.powers,bind_tc_ok,JGs_LibraScale0.source,
    JGs_LibraStage0.term0,JGs_LibraStage0.term1,JGs_LibraStage0.term2,JGs_LibraStage0.term3,JGs_LibraStage0.totals,JGs_LibraStage0.finish]
#print axioms step0
theorem step1 : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {start:=1#usize,«end»:=2#usize} JGs_LibraEnd.middle=
    ok (.cont ({start:=2#usize,«end»:=2#usize},JGs_LibraEnd.value)) := by
  rw [JGs_LibraProgram.source]
  unfold JGs_LibraProgram.body
  rw [JGo_TX2_Range.next 1#usize 2#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,JGs_LibraStage1.powers,bind_tc_ok,JGs_LibraScale1.source,
    JGs_LibraStage1.term0,JGs_LibraStage1.term1,JGs_LibraStage1.term2,JGs_LibraStage1.term3,JGs_LibraStage1.totals,JGs_LibraStage1.finish]
#print axioms step1
end AspisR1.JGs_LibraNative
end
