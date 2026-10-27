import RPt_FJi_TermValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_TermRead
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations
/-- Expose only the decoder call of the SAME reached term step. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter next : FIo_RangeNext.Range) (s out : Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter s=
      ok (.cont (next,out))) :
    ∃ term x,term.val=iter.start.val ∧ JFr_TX2_ScalarRead.read q slot term=ok x := by
  rw [JFr_TX2_DotStep.body] at run
  unfold JFr_TX2_DotStep.step at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some term =>
    obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨s1,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have pr := FIo_RangeNext.some_next iter next term hn
    exact ⟨term,x,congrArg UScalar.val pr.1,hx⟩
#print axioms value
end AspisR1.FJl_TermRead
end
