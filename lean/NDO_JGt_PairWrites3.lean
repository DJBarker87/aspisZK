import NDO_JGt_ContractionStep
import NDO_JGt_PairWrites2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairWrites
open Aeneas Aeneas.Std Result ControlFlow
def product3 : E := ⟨⟨⟨349029496#u32,1025458631#u32⟩,⟨1052961092#u32,341435914#u32⟩⟩,⟨⟨749031285#u32,2135859702#u32⟩,⟨288991240#u32,1698411974#u32⟩⟩⟩
def v4 : E := ⟨⟨⟨2105401063#u32,321124502#u32⟩,⟨563709960#u32,1939621204#u32⟩⟩,⟨⟨1881297439#u32,287073032#u32⟩,⟨270173912#u32,621447372#u32⟩⟩⟩
def p4 : Array E 7#usize := initial.set 4#usize v4
theorem mul3 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul (FIo_Install.toE JGo_TX2_Message00.value03) (JGs_LibraEnd.value.val[3])=ok product3 := by with_unfolding_all rfl
#print axioms mul3
theorem add3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v3 product3=ok v4 := by with_unfolding_all rfl
#print axioms add3
theorem step3 : FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value
    {start:=3#usize,«end»:=4#usize} p3=ok (.cont ({start:=4#usize,«end»:=4#usize},p4)) := by
  have read : Array.index_usize p3 4#usize=ok v3 := by with_unfolding_all rfl
  have lr : Array.index_usize JGs_LibraEnd.value 3#usize=ok (JGs_LibraEnd.value.val[3]) := by rfl
  exact JGt_ContractionStep.step8 JGq_PairShape.f JGs_LibraEnd.value p3
    3#usize 4#usize _ _ _ _ _
    (JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide)) read
    JGo_TX2_Message00.native_field03 lr mul3 add3
#print axioms step3
end AspisR1.JGt_PairWrites
end
