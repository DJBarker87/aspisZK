import RPu_FJf_PointCell
import RPt_FIp_RangeNone
set_option autoImplicit false
namespace AspisR1.FJf_PointDone
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
theorem done (points : Points) (k : Usize) (iter : FIo_RangeNext.Range)
    (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=ok (.done out)) :
    iter.end.val ≤ iter.start.val ∧ out=factors := by
  unfold FIn_WeightsExtract.weights_new_loop0_loop0.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some d =>
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms done
end AspisR1.FJf_PointDone
