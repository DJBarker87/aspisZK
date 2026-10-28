import NDO_JGt_SumStep
import NDO_JGt_PairWrites
import NDO_JGq_PowersK
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairSum
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
def v0 : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def product0 : E := ⟨⟨⟨350438595#u32,491793781#u32⟩,⟨1113861523#u32,1192423184#u32⟩⟩,⟨⟨1739471909#u32,493835793#u32⟩,⟨652325089#u32,828623136#u32⟩⟩⟩
def v1 : E := ⟨⟨⟨350438595#u32,491793781#u32⟩,⟨1113861523#u32,1192423184#u32⟩⟩,⟨⟨1739471909#u32,493835793#u32⟩,⟨652325089#u32,828623136#u32⟩⟩⟩
theorem mul0 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_PowersK.p0 (JGt_PairWrites.p4.val[0])=ok product0 := by with_unfolding_all rfl
#print axioms mul0
theorem add0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add v0 product0=ok v1 := by with_unfolding_all rfl
#print axioms add0
theorem step0 : FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7
    {start:=0#usize,«end»:=7#usize} v0=ok (.cont ({start:=1#usize,«end»:=7#usize},v1)) := by
  have read : Array.index_usize JGt_PairWrites.p4 0#usize=ok (JGt_PairWrites.p4.val[0]) := by rfl
  have power : Array.index_usize JGq_PowersK.a7 0#usize=ok JGq_PowersK.p0 := by rfl
  exact JGt_SumStep.source JGt_PairWrites.p4 JGq_PowersK.a7 0#usize 1#usize v0 _ _ _ _
    (JGo_TX2_Range.next 0#usize 7#usize 1#usize (by decide) (by decide)) read power mul0 add0
#print axioms step0
end AspisR1.JGt_PairSum
end
