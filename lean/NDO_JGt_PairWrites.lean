import NDO_JGt_PairWrites3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_PairWrites
open Aeneas Aeneas.Std Result ControlFlow
abbrev S := core.ops.range.Range Usize × Array E 7#usize
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=4#usize},initial)
  | 1 => ({start:=1#usize,«end»:=4#usize},p1)
  | 2 => ({start:=2#usize,«end»:=4#usize},p2)
  | 3 => ({start:=3#usize,«end»:=4#usize},p3)
  | _ => ({start:=4#usize,«end»:=4#usize},p4)
theorem source : FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} JGq_PairShape.f initial JGs_LibraEnd.value=ok p4 := by
  unfold FIo_Native.weights.Weights.pair_loop8
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.Weights.pair_loop8.body JGq_PairShape.f JGs_LibraEnd.value t.1 t.2) states 4 p4
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
  · unfold FIo_Native.weights.Weights.pair_loop8.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGt_PairWrites
end
