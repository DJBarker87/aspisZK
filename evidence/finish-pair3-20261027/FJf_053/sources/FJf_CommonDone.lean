import FJf_CommonCell
import FIp_RangeNone
set_option autoImplicit false
namespace AspisR1.FJf_CommonDone
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
theorem done (self : FIo_Native.weights.Weights) (iter : FIo_RangeNext.Range)
    (common : Array NQ 16#usize) (out : FIo_Native.weights.Weights × Array NQ 16#usize)
    (run : FIo_Native.weights.Weights.pair_loop1.body self iter common=ok (.done out)) :
    iter.end.val ≤ iter.start.val ∧ out=(self,common) := by
  unfold FIo_Native.weights.Weights.pair_loop1.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some j =>
    simp only [lift,bind_tc_ok] at run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms done
end AspisR1.FJf_CommonDone
