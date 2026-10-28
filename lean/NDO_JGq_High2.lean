import NDO_JGq_HighData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_High
open Aeneas Aeneas.Std Result ControlFlow
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push d2_0
    JGq_Partial.value0 c2_0=ok (.Ok (),d2_1) := by
  have inc : Usize.wrapping_add d2_0.count 1#usize=1#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_0.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_0
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push d2_1
    JGq_Partial.value1 c2_1=ok (.Ok (),d2_2) := by
  have inc : Usize.wrapping_add d2_1.count 1#usize=2#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_1.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push d2_2
    JGq_Partial.value2 c2_2=ok (.Ok (),d2_3) := by
  have inc : Usize.wrapping_add d2_2.count 1#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_2.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_2
theorem push2_3 : FIo_Native.fast_pairing.EbyKDot.push d2_3
    JGq_Partial.value3 c2_3=ok (.Ok (),d2_4) := by
  have inc : Usize.wrapping_add d2_3.count 1#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d2_3.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push2_3
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish d2_4=ok high2 := by with_unfolding_all rfl
#print axioms finish2
theorem step2_0 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row2
    {start:=0#usize,«end»:=4#usize} d2_0=
    ok (.cont ({start:=1#usize,«end»:=4#usize},d2_1)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 0#usize=ok JGq_Partial.value0 := by rfl
  have rq : Array.index_usize row2 0#usize=ok c2_0 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push2_0,bind_tc_ok]
  rfl
#print axioms step2_0
theorem step2_1 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row2
    {start:=1#usize,«end»:=4#usize} d2_1=
    ok (.cont ({start:=2#usize,«end»:=4#usize},d2_2)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 1#usize=ok JGq_Partial.value1 := by rfl
  have rq : Array.index_usize row2 1#usize=ok c2_1 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push2_1,bind_tc_ok]
  rfl
#print axioms step2_1
theorem step2_2 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row2
    {start:=2#usize,«end»:=4#usize} d2_2=
    ok (.cont ({start:=3#usize,«end»:=4#usize},d2_3)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 2#usize=ok JGq_Partial.value2 := by rfl
  have rq : Array.index_usize row2 2#usize=ok c2_2 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push2_2,bind_tc_ok]
  rfl
#print axioms step2_2
theorem step2_3 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row2
    {start:=3#usize,«end»:=4#usize} d2_3=
    ok (.cont ({start:=4#usize,«end»:=4#usize},d2_4)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 3#usize=ok JGq_Partial.value3 := by rfl
  have rq : Array.index_usize row2 3#usize=ok c2_3 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push2_3,bind_tc_ok]
  rfl
#print axioms step2_3
abbrev S2 := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states2 : Nat → S2
  | 0 => ({start:=0#usize,«end»:=4#usize},d2_0)
  | 1 => ({start:=1#usize,«end»:=4#usize},d2_1)
  | 2 => ({start:=2#usize,«end»:=4#usize},d2_2)
  | 3 => ({start:=3#usize,«end»:=4#usize},d2_3)
  | _ => ({start:=4#usize,«end»:=4#usize},d2_4)
theorem source2 : FIo_Native.weights.high_dot JGq_SharedPartials.value row2=ok (.Ok high2) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d2_0 := by rfl
  unfold FIo_Native.weights.high_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.high_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S2=>FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row2 x.1 x.2)
    states2 4 (.Ok high2)
  · intro i hi
    interval_cases i
    · exact step2_0
    · exact step2_1
    · exact step2_2
    · exact step2_3
  · change FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row2
        {start:=4#usize,«end»:=4#usize} d2_4=ok (.done (.Ok high2))
    unfold FIo_Native.weights.high_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=4#usize,«end»:=4#usize} : core.ops.range.Range Usize)=ok (none,{start:=4#usize,«end»:=4#usize}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish2,bind_tc_ok]
#print axioms source2
end AspisR1.JGq_High
end
