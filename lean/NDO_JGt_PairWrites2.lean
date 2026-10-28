import NDO_JGt_ContractionStep
import NDO_JGt_PairWrites1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairWrites
open Aeneas Aeneas.Std Result ControlFlow
def product2 : E := ⟨⟨⟨1432831535#u32,972267670#u32⟩,⟨1844650417#u32,772564503#u32⟩⟩,⟨⟨2005653577#u32,1408949465#u32⟩,⟨1903690481#u32,451817205#u32⟩⟩⟩
def v3 : E := ⟨⟨⟨1756371567#u32,1443149518#u32⟩,⟨1658232515#u32,1598185290#u32⟩⟩,⟨⟨1132266154#u32,298696977#u32⟩,⟨2128666319#u32,1070519045#u32⟩⟩⟩
def p3 : Array E 7#usize := initial.set 4#usize v3
theorem mul2 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul (FIo_Install.toE JGo_TX2_Message00.value02) (JGs_LibraEnd.value.val[2])=ok product2 := by with_unfolding_all rfl
#print axioms mul2
theorem add2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v2 product2=ok v3 := by with_unfolding_all rfl
#print axioms add2
theorem step2 : FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value
    {start:=2#usize,«end»:=4#usize} p2=ok (.cont ({start:=3#usize,«end»:=4#usize},p3)) := by
  have read : Array.index_usize p2 4#usize=ok v2 := by with_unfolding_all rfl
  have lr : Array.index_usize JGs_LibraEnd.value 2#usize=ok (JGs_LibraEnd.value.val[2]) := by rfl
  exact JGt_ContractionStep.step8 JGq_PairShape.f JGs_LibraEnd.value p2
    2#usize 3#usize _ _ _ _ _
    (JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide)) read
    JGo_TX2_Message00.native_field02 lr mul2 add2
#print axioms step2
end AspisR1.JGt_PairWrites
end
