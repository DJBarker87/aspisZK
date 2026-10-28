import NDO_JGt_SumStep
import NDO_JGt_PairSum3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairSum
open Aeneas Aeneas.Std Result ControlFlow
def product4 : E := ⟨⟨⟨1874877763#u32,925001421#u32⟩,⟨1143748985#u32,1754822256#u32⟩⟩,⟨⟨1766354780#u32,2122719921#u32⟩,⟨1509596273#u32,725722375#u32⟩⟩⟩
def v5 : E := ⟨⟨⟨416502819#u32,1367207171#u32⟩,⟨392874317#u32,190560850#u32⟩⟩,⟨⟨402773038#u32,1813047631#u32⟩,⟨373493300#u32,62658545#u32⟩⟩⟩
theorem mul4 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p4 (JGt_PairWrites.p4.val[4])=ok product4 := by with_unfolding_all rfl
#print axioms mul4
theorem add4 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v4 product4=ok v5 := by with_unfolding_all rfl
#print axioms add4
theorem step4 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=4#usize,«end»:=7#usize} v4=ok (.cont ({start:=5#usize,«end»:=7#usize},v5)) := by
  have read : Array.index_usize JGt_PairWrites.p4 4#usize=ok (JGt_PairWrites.p4.val[4]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 4#usize=ok JGq_PowersK.p4 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 4#usize 5#usize v4 _ _ _ _
    (JGo_TX2_Range.next 4#usize 7#usize 5#usize (by decide) (by decide)) read power mul4 add4
#print axioms step4
end AspisR1.JGt_PairSum
end
