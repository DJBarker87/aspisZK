import FJj_TensorInnerFull
import FJj_TensorWidth
import FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorOuterCell
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)

theorem value (self selfOut : FIo_Native.weights.Weights) (k d n nOut : Usize)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize self.factors k=ok row) (hd : Array.index_usize row d=ok digit)
    (hn : n.val≤16) (np : 0<n.val) (input out : Slice NQ)
    (hc : FJf_QMArray.canon digit) (hs : FJj_QMSlice.canon input)
    (iter cursor : FIo_RangeNext.Range)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some d,cursor))
    (run : FIo_Native.weights.Weights.tensor_loop0.body k iter self input n=
      ok (.cont (cursor,selfOut,out,nOut))) :
    selfOut=self ∧ FJj_QMSlice.canon out ∧ out.val.length=input.val.length ∧ nOut.val=4*n.val ∧
      ∀ t,t<4*n.val → FJj_QMSlice.value out t=
        FJj_QMSlice.value input (t%n.val)*FJf_QMArray.value digit (t/n.val) := by
  unfold FIo_Native.weights.Weights.tensor_loop0.body at run
  rw [hnext] at run
  simp only [bind_tc_ok] at run
  obtain ⟨rev,hrev,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have er : rev=FJa_ReverseStep.cursor n := (Result.ok.inj hrev).symm
  subst rev
  obtain ⟨⟨self1,output⟩,hinner,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  simp only [lift,bind_tc_ok] at run
  cases Result.ok.inj run
  have result := FJj_TensorInnerFull.value self selfOut k d n row digit hr hd hn np input out hc hs hinner
  refine ⟨result.1,result.2.1,result.2.2.1,?_,result.2.2.2⟩
  exact FJj_TensorWidth.value n hn
#print axioms value
end AspisR1.FJj_TensorOuterCell
end
