import NDO_JGt_SumStep
import NDO_JGt_PairSum4
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_PairSum
open Aeneas Aeneas.Std Result ControlFlow
open JGt_PairSum
def product5 : E := ⟨⟨⟨1795900638#u32,1180361385#u32⟩,⟨1900308405#u32,1322387870#u32⟩⟩,⟨⟨593167046#u32,546105727#u32⟩,⟨1607807585#u32,1182690837#u32⟩⟩⟩
def v6 : E := ⟨⟨⟨64919810#u32,400084909#u32⟩,⟨145699075#u32,1512948720#u32⟩⟩,⟨⟨995940084#u32,211669711#u32⟩,⟨1981300885#u32,1245349382#u32⟩⟩⟩
theorem mul5 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p5 (JGt_PairWrites.p4.val[5])=ok product5 := by with_unfolding_all rfl
#print axioms mul5
theorem add5 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v5 product5=ok v6 := by with_unfolding_all rfl
#print axioms add5
theorem step5 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=5#usize,«end»:=7#usize} v5=ok (.cont ({start:=6#usize,«end»:=7#usize},v6)) := by
  have read : Array.index_usize JGt_PairWrites.p4 5#usize=ok (JGt_PairWrites.p4.val[5]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 5#usize=ok JGq_PowersK.p5 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 5#usize 6#usize v5 _ _ _ _
    (JGo_TX2_Range.next 5#usize 7#usize 6#usize (by decide) (by decide)) read power mul5 add5
#print axioms step5
end AspisR1.JGv_PairSum
end
