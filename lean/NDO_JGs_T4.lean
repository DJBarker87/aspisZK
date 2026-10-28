import NDO_JGs_T4Step0
import NDO_JGs_T4Step1
import NDO_JGs_T4Step2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T4
open Aeneas Aeneas.Std Result ControlFlow
def states2 : Nat → FJa_ReverseStep.Rev × Slice FIo_Install.NQ
  | 0 => (FJa_ReverseStep.cursor 1#usize,s0)
  | _ => (FJa_ReverseStep.cursor 0#usize,s1)
theorem inner2 : FIo_Native.weights.Weights.tensor_loop0_loop0 (FJa_ReverseStep.cursor 1#usize)
    JGq_PairShape.w 4#usize s0 1#usize 2#usize=ok (JGq_PairShape.w,s1) := by
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : FJa_ReverseStep.Rev × Slice FIo_Install.NQ=>FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 4#usize 1#usize 2#usize t.1 t.2)
    states2 1 (JGq_PairShape.w,s1)
  · intro i hi
    interval_cases i
    · exact step0
  · change FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 4#usize 1#usize 2#usize (FJa_ReverseStep.cursor 0#usize) s1=ok (.done (JGq_PairShape.w,s1))
    unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
    have stop := FJa_ReverseStep.stop
    unfold FJa_ReverseStep.next at stop
    rw [stop,bind_tc_ok]
    rfl
#print axioms inner2
theorem outer2 : FIo_Native.weights.Weights.tensor_loop0.body 4#usize
    {start:=2#usize,«end»:=5#usize} JGq_PairShape.w s0 1#usize=
    ok (.cont ({start:=3#usize,«end»:=5#usize},JGq_PairShape.w,s1,4#usize)) := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body
  rw [JGo_TX2_Range.next 2#usize 5#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have rev : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ({start:=0#usize,«end»:=1#usize} : core.ops.range.Range Usize)=ok (FJa_ReverseStep.cursor 1#usize) := by rfl
  rw [rev,bind_tc_ok,inner2,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok]
  have wrap : Usize.wrapping_mul 1#usize 4#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 4#usize (by decide))
  rw [wrap]
#print axioms outer2
def states3 : Nat → FJa_ReverseStep.Rev × Slice FIo_Install.NQ
  | 0 => (FJa_ReverseStep.cursor 4#usize,s1)
  | 1 => (FJa_ReverseStep.cursor 3#usize,s2)
  | 2 => (FJa_ReverseStep.cursor 2#usize,s3)
  | 3 => (FJa_ReverseStep.cursor 1#usize,s4)
  | _ => (FJa_ReverseStep.cursor 0#usize,s5)
theorem inner3 : FIo_Native.weights.Weights.tensor_loop0_loop0 (FJa_ReverseStep.cursor 4#usize)
    JGq_PairShape.w 4#usize s1 4#usize 3#usize=ok (JGq_PairShape.w,s5) := by
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : FJa_ReverseStep.Rev × Slice FIo_Install.NQ=>FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 4#usize 4#usize 3#usize t.1 t.2)
    states3 4 (JGq_PairShape.w,s5)
  · intro i hi
    interval_cases i
    · exact step1
    · exact step2
    · exact step3
    · exact step4
  · change FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 4#usize 4#usize 3#usize (FJa_ReverseStep.cursor 0#usize) s5=ok (.done (JGq_PairShape.w,s5))
    unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
    have stop := FJa_ReverseStep.stop
    unfold FJa_ReverseStep.next at stop
    rw [stop,bind_tc_ok]
    rfl
#print axioms inner3
theorem outer3 : FIo_Native.weights.Weights.tensor_loop0.body 4#usize
    {start:=3#usize,«end»:=5#usize} JGq_PairShape.w s1 4#usize=
    ok (.cont ({start:=4#usize,«end»:=5#usize},JGq_PairShape.w,s5,16#usize)) := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body
  rw [JGo_TX2_Range.next 3#usize 5#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have rev : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ({start:=0#usize,«end»:=4#usize} : core.ops.range.Range Usize)=ok (FJa_ReverseStep.cursor 4#usize) := by rfl
  rw [rev,bind_tc_ok,inner3,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok]
  have wrap : Usize.wrapping_mul 4#usize 4#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 4#usize 4#usize (by decide))
  rw [wrap]
#print axioms outer3
def states4 : Nat → FJa_ReverseStep.Rev × Slice FIo_Install.NQ
  | 0 => (FJa_ReverseStep.cursor 16#usize,s5)
  | 1 => (FJa_ReverseStep.cursor 15#usize,s6)
  | 2 => (FJa_ReverseStep.cursor 14#usize,s7)
  | 3 => (FJa_ReverseStep.cursor 13#usize,s8)
  | 4 => (FJa_ReverseStep.cursor 12#usize,s9)
  | 5 => (FJa_ReverseStep.cursor 11#usize,s10)
  | 6 => (FJa_ReverseStep.cursor 10#usize,s11)
  | 7 => (FJa_ReverseStep.cursor 9#usize,s12)
  | 8 => (FJa_ReverseStep.cursor 8#usize,s13)
  | 9 => (FJa_ReverseStep.cursor 7#usize,s14)
  | 10 => (FJa_ReverseStep.cursor 6#usize,s15)
  | 11 => (FJa_ReverseStep.cursor 5#usize,s16)
  | 12 => (FJa_ReverseStep.cursor 4#usize,s17)
  | 13 => (FJa_ReverseStep.cursor 3#usize,s18)
  | 14 => (FJa_ReverseStep.cursor 2#usize,s19)
  | 15 => (FJa_ReverseStep.cursor 1#usize,s20)
  | _ => (FJa_ReverseStep.cursor 0#usize,s21)
theorem inner4 : FIo_Native.weights.Weights.tensor_loop0_loop0 (FJa_ReverseStep.cursor 16#usize)
    JGq_PairShape.w 4#usize s5 16#usize 4#usize=ok (JGq_PairShape.w,s21) := by
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : FJa_ReverseStep.Rev × Slice FIo_Install.NQ=>FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 4#usize 16#usize 4#usize t.1 t.2)
    states4 16 (JGq_PairShape.w,s21)
  · intro i hi
    interval_cases i
    · exact step5
    · exact step6
    · exact step7
    · exact step8
    · exact step9
    · exact step10
    · exact step11
    · exact step12
    · exact step13
    · exact step14
    · exact step15
    · exact step16
    · exact step17
    · exact step18
    · exact step19
    · exact step20
  · change FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 4#usize 16#usize 4#usize (FJa_ReverseStep.cursor 0#usize) s21=ok (.done (JGq_PairShape.w,s21))
    unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
    have stop := FJa_ReverseStep.stop
    unfold FJa_ReverseStep.next at stop
    rw [stop,bind_tc_ok]
    rfl
#print axioms inner4
theorem outer4 : FIo_Native.weights.Weights.tensor_loop0.body 4#usize
    {start:=4#usize,«end»:=5#usize} JGq_PairShape.w s5 16#usize=
    ok (.cont ({start:=5#usize,«end»:=5#usize},JGq_PairShape.w,s21,64#usize)) := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body
  rw [JGo_TX2_Range.next 4#usize 5#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have rev : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      ({start:=0#usize,«end»:=16#usize} : core.ops.range.Range Usize)=ok (FJa_ReverseStep.cursor 16#usize) := by rfl
  rw [rev,bind_tc_ok,inner4,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok]
  have wrap : Usize.wrapping_mul 16#usize 4#usize=64#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 4#usize (by decide))
  rw [wrap]
#print axioms outer4
abbrev S := core.ops.range.Range Usize × FIo_Native.weights.Weights × Slice FIo_Install.NQ × Usize
def outerStates : Nat → S
  | 0 => ({start:=2#usize,«end»:=5#usize},JGq_PairShape.w,s0,1#usize)
  | 1 => ({start:=3#usize,«end»:=5#usize},JGq_PairShape.w,s1,4#usize)
  | 2 => ({start:=4#usize,«end»:=5#usize},JGq_PairShape.w,s5,16#usize)
  | _ => ({start:=5#usize,«end»:=5#usize},JGq_PairShape.w,s21,64#usize)
theorem source : FIo_Native.weights.Weights.tensor JGq_PairShape.w 4#usize 2#usize input=ok s21 := by
  have init : Slice.update input 0#usize FIo_Native.aspis_core.field.QM31.ONE=ok s0 := by with_unfolding_all rfl
  unfold FIo_Native.weights.Weights.tensor
  rw [init,bind_tc_ok]
  unfold FIo_Native.weights.Weights.tensor_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : S=>FIo_Native.weights.Weights.tensor_loop0.body 4#usize t.1 t.2.1 t.2.2.1 t.2.2.2)
    outerStates 3 s21
  · intro i hi
    interval_cases i
    · exact outer2
    · exact outer3
    · exact outer4
  · unfold FIo_Native.weights.Weights.tensor_loop0.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGs_T4
end
