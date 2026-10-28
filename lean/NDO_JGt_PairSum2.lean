import NDO_JGt_SumStep
import NDO_JGt_PairSum1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairSum
open Aeneas Aeneas.Std Result ControlFlow
def product2 : E := ⟨⟨⟨580102180#u32,1064291749#u32⟩,⟨2019353930#u32,1268711432#u32⟩⟩,⟨⟨1089823569#u32,2124733316#u32⟩,⟨685101167#u32,154979631#u32⟩⟩⟩
def v3 : E := ⟨⟨⟨379295725#u32,1584261910#u32⟩,⟨475690860#u32,2062767164#u32⟩⟩,⟨⟨357123958#u32,336880742#u32⟩,⟨603211899#u32,1401339237#u32⟩⟩⟩
theorem mul2 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p2 (JGt_PairWrites.p4.val[2])=ok product2 := by with_unfolding_all rfl
#print axioms mul2
theorem add2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v2 product2=ok v3 := by with_unfolding_all rfl
#print axioms add2
theorem step2 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=2#usize,«end»:=7#usize} v2=ok (.cont ({start:=3#usize,«end»:=7#usize},v3)) := by
  have read : Array.index_usize JGt_PairWrites.p4 2#usize=ok (JGt_PairWrites.p4.val[2]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 2#usize=ok JGq_PowersK.p2 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 2#usize 3#usize v2 _ _ _ _
    (JGo_TX2_Range.next 2#usize 7#usize 3#usize (by decide) (by decide)) read power mul2 add2
#print axioms step2
end AspisR1.JGt_PairSum
end
