import NDO_JGt_SumStep
import NDO_JGt_PairSum2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairSum
open Aeneas Aeneas.Std Result ControlFlow
def product3 : E := ⟨⟨⟨309812978#u32,1005427487#u32⟩,⟨920918119#u32,667938724#u32⟩⟩,⟨⟨426777947#u32,1500930615#u32⟩,⟨408168775#u32,83080580#u32⟩⟩⟩
def v4 : E := ⟨⟨⟨689108703#u32,442205750#u32⟩,⟨1396608979#u32,583222241#u32⟩⟩,⟨⟨783901905#u32,1837811357#u32⟩,⟨1011380674#u32,1484419817#u32⟩⟩⟩
theorem mul3 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p3 (JGt_PairWrites.p4.val[3])=ok product3 := by with_unfolding_all rfl
#print axioms mul3
theorem add3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v3 product3=ok v4 := by with_unfolding_all rfl
#print axioms add3
theorem step3 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=3#usize,«end»:=7#usize} v3=ok (.cont ({start:=4#usize,«end»:=7#usize},v4)) := by
  have read : Array.index_usize JGt_PairWrites.p4 3#usize=ok (JGt_PairWrites.p4.val[3]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 3#usize=ok JGq_PowersK.p3 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 3#usize 4#usize v3 _ _ _ _
    (JGo_TX2_Range.next 3#usize 7#usize 4#usize (by decide) (by decide)) read power mul3 add3
#print axioms step3
end AspisR1.JGt_PairSum
end
