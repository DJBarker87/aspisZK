import NDO_JGt_SumStep
import NDO_JGt_PairSum0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairSum
open Aeneas Aeneas.Std Result ControlFlow
def product1 : E := ⟨⟨⟨1596238597#u32,28176380#u32⟩,⟨1637442701#u32,1749116195#u32⟩⟩,⟨⟨1822795774#u32,2013278927#u32⟩,⟨1413269290#u32,417736470#u32⟩⟩⟩
def v2 : E := ⟨⟨⟨1946677192#u32,519970161#u32⟩,⟨603820577#u32,794055732#u32⟩⟩,⟨⟨1414784036#u32,359631073#u32⟩,⟨2065594379#u32,1246359606#u32⟩⟩⟩
theorem mul1 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p1 (JGt_PairWrites.p4.val[1])=ok product1 := by with_unfolding_all rfl
#print axioms mul1
theorem add1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v1 product1=ok v2 := by with_unfolding_all rfl
#print axioms add1
theorem step1 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=1#usize,«end»:=7#usize} v1=ok (.cont ({start:=2#usize,«end»:=7#usize},v2)) := by
  have read : Array.index_usize JGt_PairWrites.p4 1#usize=ok (JGt_PairWrites.p4.val[1]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 1#usize=ok JGq_PowersK.p1 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 1#usize 2#usize v1 _ _ _ _
    (JGo_TX2_Range.next 1#usize 7#usize 2#usize (by decide) (by decide)) read power mul1 add1
#print axioms step1
end AspisR1.JGt_PairSum
end
