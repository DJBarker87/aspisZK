import NDO_JGt_ContractionStep
import NDO_JGt_PairWrites0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairWrites
open Aeneas Aeneas.Std Result ControlFlow
def product1 : E := ⟨⟨⟨1398749116#u32,1060995226#u32⟩,⟨336445712#u32,2045964429#u32⟩⟩,⟨⟨1086462225#u32,1188989653#u32⟩,⟨1596501660#u32,443100952#u32⟩⟩⟩
def v2 : E := ⟨⟨⟨323540032#u32,470881848#u32⟩,⟨1961065745#u32,825620787#u32⟩⟩,⟨⟨1274096224#u32,1037231159#u32⟩,⟨224975838#u32,618701840#u32⟩⟩⟩
def p2 : Array E 7#usize := initial.set 4#usize v2
theorem mul1 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul (FIo_Install.toE JGo_TX2_Message00.value01) (JGs_LibraEnd.value.val[1])=ok product1 := by with_unfolding_all rfl
#print axioms mul1
theorem add1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v1 product1=ok v2 := by with_unfolding_all rfl
#print axioms add1
theorem step1 : FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value
    {start:=1#usize,«end»:=4#usize} p1=ok (.cont ({start:=2#usize,«end»:=4#usize},p2)) := by
  have read : Array.index_usize p1 4#usize=ok v1 := by with_unfolding_all rfl
  have lr : Array.index_usize JGs_LibraEnd.value 1#usize=ok (JGs_LibraEnd.value.val[1]) := by rfl
  exact JGt_ContractionStep.step8 JGq_PairShape.f JGs_LibraEnd.value p1
    1#usize 2#usize _ _ _ _ _
    (JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide)) read
    JGo_TX2_Message00.native_field01 lr mul1 add1
#print axioms step1
end AspisR1.JGt_PairWrites
end
