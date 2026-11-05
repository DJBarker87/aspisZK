import NIW_AlignFinalCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinalTraceLog
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition NIW_AlignFinalCollect

/-- The witness records exactly which supplied chronological event belongs to
which constructor, including the full mutable before/after arrays. -/
inductive TraceLog (parts powers : Parts) : Nat → NHX_FinalLoop.State → List Event → E → Prop
 | done (fuel : Nat) (s : NHX_FinalLoop.State) (stop : s.1.end.val≤s.1.start.val) :
   TraceLog parts powers (fuel+1) s [] s.2
 | step (fuel : Nat) (s : NHX_FinalLoop.State) (out : E)
   (after : E) (log : Final) (events : List Event) (last : s.1.end.val=7)
   (cut : cutFinal parts powers s.1.start.val s.2 log after)
   (law : EMul log.mul_a log.mul_b log.product) (scale : EAdd log.add_a log.add_b log.reply) (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : TraceLog parts powers fuel (rest,after) events out) :
   TraceLog parts powers (fuel+1) s (⟨s.1.start,s.2,ok (after,log)⟩::events) out

theorem forget (parts powers : Parts) (fuel : Nat) (s : NHX_FinalLoop.State)
 (events : List Event) (out : E) (trace : TraceLog parts powers fuel s events out) :
 NIT_PairComposition.FinalTrace parts powers fuel s out := by
 induction trace with
 | done fuel s stop => exact .done fuel s stop
 | step fuel s out after log events last cut law scale rest next tail ih =>
  exact .step fuel s out after log cut law scale rest next ih

/-- A source stream determines the constructor's exact logs, not just its
final array. No fresh log or endpoint-equality premise is introduced. -/
theorem collected (parts powers : Parts) (h0 : canonical parts) (h1 : canonical powers) (fuel : Nat)
 (s : NHX_FinalLoop.State) (last : s.1.end.val=7) (bound : s.1.start.val≤7)
 (hc : canonE s.2) (enough : 7-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect parts powers fuel s).1
  (fun out=>TraceLog parts powers fuel s (collect parts powers fuel s).2 out ∧ canonE out) := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
  by_cases active : s.1.start.val<7
  · obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
    have obs := NIW_AlignFinalExecution.observed parts powers h0 h1 s.1.start active s.2 hc
    cases call : NIW_AlignFinalExecution.step parts powers s.1.start s.2 with
    | fail err => simp only [call,NIW_AlignFieldReply.Produced] at obs
    | div => simp only [call,NIW_AlignFieldReply.Produced] at obs
    | ok value =>
     rcases value with ⟨after,log⟩
     simp only [call,NIW_AlignFieldReply.Produced] at obs
     have tail := ih (rest,after) (by simpa only [he] using last)
      (by change rest.start.val≤7;omega) obs.2.2.2
      (by change 7-rest.start.val<fuel;omega)
     cases result : (collect parts powers fuel (rest,after)).1 with
     | fail err => simp only [result,NIW_AlignFieldReply.Produced] at tail
     | div => simp only [result,NIW_AlignFieldReply.Produced] at tail
     | ok out =>
      simp only [result,NIW_AlignFieldReply.Produced] at tail
      simp only [collect,next,call,result,NIW_AlignFieldReply.Produced]
      exact ⟨.step fuel s out after log _ last obs.1 obs.2.1 obs.2.2.1 rest next tail.1,tail.2⟩
  · have stop : s.1.end.val≤s.1.start.val := by omega
    have next := NHI_ForwardRange.done s.1 stop
    simp only [collect,next,NIW_AlignFieldReply.Produced]
    exact ⟨.done fuel s stop,hc⟩

#print axioms forget
#print axioms collected
end AspisR1.NIW_AlignFinalTraceLog
