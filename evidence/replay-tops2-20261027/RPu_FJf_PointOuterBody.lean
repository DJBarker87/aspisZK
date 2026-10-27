import RPu_FJf_PointFrame
set_option autoImplicit false
namespace AspisR1.FJf_PointOuterBody
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)

theorem cont (points : Points) (iter cursor : FIo_RangeNext.Range) (factors next : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0.body points iter factors=ok (.cont (cursor,next))) :
    ∃ k, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some k,cursor) ∧
      FIn_WeightsExtract.weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize}
        points factors k=ok next := by
  unfold FIn_WeightsExtract.weights_new_loop0.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some k =>
    obtain ⟨f,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    exact ⟨k,hn,hf⟩

theorem done (points : Points) (iter : FIo_RangeNext.Range) (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0.body points iter factors=ok (.done out)) :
    iter.end.val ≤ iter.start.val ∧ out=factors := by
  unfold FIn_WeightsExtract.weights_new_loop0.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some k =>
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms cont
#print axioms done
end AspisR1.FJf_PointOuterBody
