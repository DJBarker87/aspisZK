import FJj_TensorInnerFull
import FIo_RangeNext
set_option autoImplicit false
namespace AspisR1.FJj_TensorOuterBody
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)

theorem cont (k n nOut : Usize) (iter cursor : FIo_RangeNext.Range)
    (self selfOut : FIo_Native.weights.Weights) (input out : Slice NQ)
    (run : FIo_Native.weights.Weights.tensor_loop0.body k iter self input n=
      ok (.cont (cursor,selfOut,out,nOut))) :
    ∃ d,core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some d,cursor) := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body at run
  obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some d =>
    obtain ⟨rev,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨self1,out1⟩,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    cases Result.ok.inj run
    exact ⟨d,hn⟩

theorem done (k n : Usize) (iter : FIo_RangeNext.Range)
    (self : FIo_Native.weights.Weights) (input out : Slice NQ)
    (run : FIo_Native.weights.Weights.tensor_loop0.body k iter self input n=ok (.done out)) :
    iter.end.val≤iter.start.val ∧ out=input := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body at run
  obtain ⟨⟨o,next⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter next hn,rfl⟩
  | some d =>
    obtain ⟨rev,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨self1,out1⟩,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    cases run
#print axioms cont
#print axioms done
end AspisR1.FJj_TensorOuterBody
