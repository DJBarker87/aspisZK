import NDO_JGv_PairSum6
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_PairSum
open Aeneas Aeneas.Std Result ControlFlow
open JGt_PairSum
abbrev S := core.ops.range.Range Usize × E
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=7#usize},v0)
  | 1 => ({start:=1#usize,«end»:=7#usize},v1)
  | 2 => ({start:=2#usize,«end»:=7#usize},v2)
  | 3 => ({start:=3#usize,«end»:=7#usize},v3)
  | 4 => ({start:=4#usize,«end»:=7#usize},v4)
  | 5 => ({start:=5#usize,«end»:=7#usize},v5)
  | 6 => ({start:=6#usize,«end»:=7#usize},v6)
  | _ => ({start:=7#usize,«end»:=7#usize},v7)
theorem source : FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} JGt_PairWrites.p4 JGq_PowersK.a7
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok v7 := by
  have zero : FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=JGt_PairSum.v0 := by with_unfolding_all rfl
  rw [zero]
  unfold FIo_Native.weights.Weights.pair_loop9
  apply JGo_TX2_LoopChain.source
    (fun t : S=>match t with | (iter,sum) => FIo_Native.weights.Weights.pair_loop9.body JGt_PairWrites.p4 JGq_PowersK.a7 iter sum) states 7 v7
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
    · exact step4
    · exact step5
    · exact step6
  · unfold FIo_Native.weights.Weights.pair_loop9.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGv_PairSum
end
