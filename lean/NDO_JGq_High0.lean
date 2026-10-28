import NDO_JGq_HighData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_High
open Aeneas Aeneas.Std Result ControlFlow
theorem push0_0 : FIo_Native.fast_pairing.EbyKDot.push d0_0
    JGq_Partial.value0 c0_0=ok (.Ok (),d0_1) := by
  have inc : Usize.wrapping_add d0_0.count 1#usize=1#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d0_0.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push0_0
theorem push0_1 : FIo_Native.fast_pairing.EbyKDot.push d0_1
    JGq_Partial.value1 c0_1=ok (.Ok (),d0_2) := by
  have inc : Usize.wrapping_add d0_1.count 1#usize=2#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d0_1.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push0_1
theorem push0_2 : FIo_Native.fast_pairing.EbyKDot.push d0_2
    JGq_Partial.value2 c0_2=ok (.Ok (),d0_3) := by
  have inc : Usize.wrapping_add d0_2.count 1#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d0_2.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push0_2
theorem push0_3 : FIo_Native.fast_pairing.EbyKDot.push d0_3
    JGq_Partial.value3 c0_3=ok (.Ok (),d0_4) := by
  have inc : Usize.wrapping_add d0_3.count 1#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d0_3.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push0_3
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish d0_4=ok high0 := by with_unfolding_all rfl
#print axioms finish0
theorem step0_0 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row0
    {start:=0#usize,«end»:=4#usize} d0_0=
    ok (.cont ({start:=1#usize,«end»:=4#usize},d0_1)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 0#usize=ok JGq_Partial.value0 := by rfl
  have rq : Array.index_usize row0 0#usize=ok c0_0 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push0_0,bind_tc_ok]
  rfl
#print axioms step0_0
theorem step0_1 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row0
    {start:=1#usize,«end»:=4#usize} d0_1=
    ok (.cont ({start:=2#usize,«end»:=4#usize},d0_2)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 1#usize=ok JGq_Partial.value1 := by rfl
  have rq : Array.index_usize row0 1#usize=ok c0_1 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push0_1,bind_tc_ok]
  rfl
#print axioms step0_1
theorem step0_2 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row0
    {start:=2#usize,«end»:=4#usize} d0_2=
    ok (.cont ({start:=3#usize,«end»:=4#usize},d0_3)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 2#usize=ok JGq_Partial.value2 := by rfl
  have rq : Array.index_usize row0 2#usize=ok c0_2 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push0_2,bind_tc_ok]
  rfl
#print axioms step0_2
theorem step0_3 : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row0
    {start:=3#usize,«end»:=4#usize} d0_3=
    ok (.cont ({start:=4#usize,«end»:=4#usize},d0_4)) := by
  have rp : Array.index_usize JGq_SharedPartials.value 3#usize=ok JGq_Partial.value3 := by rfl
  have rq : Array.index_usize row0 3#usize=ok c0_3 := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push0_3,bind_tc_ok]
  rfl
#print axioms step0_3
abbrev S0 := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states0 : Nat → S0
  | 0 => ({start:=0#usize,«end»:=4#usize},d0_0)
  | 1 => ({start:=1#usize,«end»:=4#usize},d0_1)
  | 2 => ({start:=2#usize,«end»:=4#usize},d0_2)
  | 3 => ({start:=3#usize,«end»:=4#usize},d0_3)
  | _ => ({start:=4#usize,«end»:=4#usize},d0_4)
theorem source0 : FIo_Native.weights.high_dot JGq_SharedPartials.value row0=ok (.Ok high0) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d0_0 := by rfl
  unfold FIo_Native.weights.high_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.high_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S0=>FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row0 x.1 x.2)
    states0 4 (.Ok high0)
  · intro i hi
    interval_cases i
    · exact step0_0
    · exact step0_1
    · exact step0_2
    · exact step0_3
  · change FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row0
        {start:=4#usize,«end»:=4#usize} d0_4=ok (.done (.Ok high0))
    unfold FIo_Native.weights.high_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=4#usize,«end»:=4#usize} : core.ops.range.Range Usize)=ok (none,{start:=4#usize,«end»:=4#usize}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish0,bind_tc_ok]
#print axioms source0
end AspisR1.JGq_High
end
