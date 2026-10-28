import NDO_JGt_ContractionStep
import NDO_JGs_K4
import NDO_JGq_SharedHigh
import NDO_JGs_Inactive
import NDO_JGs_LibraSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairWrites
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
def initial : Array E 7#usize := (JGq_SharedHigh.write JGs_K4.parts).set 0#usize JGs_Inactive.pair12
def product0 : E := ⟨⟨⟨1072274563#u32,1557370269#u32⟩,⟨1624620033#u32,927140005#u32⟩⟩,⟨⟨187633999#u32,1995725153#u32⟩,⟨775957825#u32,175600888#u32⟩⟩⟩
def v1 : E := ⟨⟨⟨1072274563#u32,1557370269#u32⟩,⟨1624620033#u32,927140005#u32⟩⟩,⟨⟨187633999#u32,1995725153#u32⟩,⟨775957825#u32,175600888#u32⟩⟩⟩
def p1 : Array E 7#usize := initial.set 4#usize v1
theorem mul0 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul (FIo_Install.toE JGo_TX2_Message00.value00) (JGs_LibraEnd.value.val[0])=ok product0 := by with_unfolding_all rfl
#print axioms mul0
theorem add0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO product0=ok v1 := by with_unfolding_all rfl
#print axioms add0
theorem step0 : FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value
    {start:=0#usize,«end»:=4#usize} initial=ok (.cont ({start:=1#usize,«end»:=4#usize},p1)) := by
  have read : Array.index_usize initial 4#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by with_unfolding_all rfl
  have lr : Array.index_usize JGs_LibraEnd.value 0#usize=ok (JGs_LibraEnd.value.val[0]) := by rfl
  exact JGt_ContractionStep.step8 JGq_PairShape.f JGs_LibraEnd.value initial
    0#usize 1#usize _ _ _ _ _
    (JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide)) read
    JGo_TX2_Message00.native_field00 lr mul0 add0
#print axioms step0
end AspisR1.JGt_PairWrites
end
