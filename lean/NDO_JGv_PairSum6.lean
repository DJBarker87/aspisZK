import NDO_JGt_SumStep
import NDO_JGv_PairSum5
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_PairSum
open Aeneas Aeneas.Std Result ControlFlow
open JGt_PairSum
def product6 : E := ⟨⟨⟨1192119331#u32,1133386725#u32⟩,⟨637488355#u32,453709713#u32⟩⟩,⟨⟨1434716182#u32,1829536764#u32⟩,⟨147374646#u32,1995001056#u32⟩⟩⟩
def v7 : E := ⟨⟨⟨1257039141#u32,1533471634#u32⟩,⟨783187430#u32,1966658433#u32⟩⟩,⟨⟨283172619#u32,2041206475#u32⟩,⟨2128675531#u32,1092866791#u32⟩⟩⟩
theorem mul6 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p6 (JGt_PairWrites.p4.val[6])=ok product6 := by with_unfolding_all rfl
#print axioms mul6
theorem add6 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v6 product6=ok v7 := by with_unfolding_all rfl
#print axioms add6
theorem step6 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=6#usize,«end»:=7#usize} v6=ok (.cont ({start:=7#usize,«end»:=7#usize},v7)) := by
  have read : Array.index_usize JGt_PairWrites.p4 6#usize=ok (JGt_PairWrites.p4.val[6]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 6#usize=ok JGq_PowersK.p6 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 6#usize 7#usize v6 _ _ _ _
    (JGo_TX2_Range.next 6#usize 7#usize 7#usize (by decide) (by decide)) read power mul6 add6
#print axioms step6
end AspisR1.JGv_PairSum
end
