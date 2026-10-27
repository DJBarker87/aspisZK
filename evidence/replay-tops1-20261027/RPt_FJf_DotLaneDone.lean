import RPt_FJf_DotLane
set_option autoImplicit false
namespace AspisR1.FJf_DotLaneDone
open Aeneas Aeneas.Std Result ControlFlow
open FJf_DotLane (Dot)
theorem done (raw : Array U64 4#usize) (iter : FIo_RangeNext.Range) (dot out : Dot)
    (run : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw iter dot=ok (.done out)) :
    iter.end.val ≤ iter.start.val ∧ out=dot := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some j =>
    obtain ⟨old,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨rv,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok] at run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms done
end AspisR1.FJf_DotLaneDone
