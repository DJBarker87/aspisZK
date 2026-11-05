import NIW_AlignLowCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLowTraceLog
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_LowChain NIW_AlignLowCollect

/-- The witness records exactly which supplied chronological event belongs to
which constructor, including the full mutable before/after arrays. -/
inductive TraceLog (ap0 ap1 : Powers) : Nat → NHX_LowDomain.State → List Event → LowCells → Prop
 | done (fuel : Nat) (s : NHX_LowDomain.State) (stop : s.1.end.val≤s.1.start.val) :
   TraceLog ap0 ap1 (fuel+1) s [] s.2
 | step (fuel : Nat) (s : NHX_LowDomain.State) (out : LowCells)
   (after : LowCells) (log : Low) (events : List Event) (last : s.1.end.val=16)
   (cut : cutLow ap0 ap1 s.1.start.val s.2 log after)
   (law : EMul log.a log.b log.product) (scale : NIT_LowInterpretation.Scale log.scale_a log.scaled) (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : TraceLog ap0 ap1 fuel (rest,after) events out) :
   TraceLog ap0 ap1 (fuel+1) s (⟨s.1.start,s.2,ok (after,log)⟩::events) out

theorem forget (ap0 ap1 : Powers) (fuel : Nat) (s : NHX_LowDomain.State)
 (events : List Event) (out : LowCells) (trace : TraceLog ap0 ap1 fuel s events out) :
 NIT_LowChain.Trace ap0 ap1 fuel s out := by
 induction trace with
 | done fuel s stop => exact .done fuel s stop
 | step fuel s out after log events last cut law scale rest next tail ih =>
  exact .step fuel s out after log last cut law scale rest next ih

/-- A source stream determines the constructor's exact logs, not just its
final array. No fresh log or endpoint-equality premise is introduced. -/
theorem collected (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1) (fuel : Nat)
 (s : NHX_LowDomain.State) (last : s.1.end.val=16) (bound : s.1.start.val≤16)
 (hc : canonical s.2) (enough : 16-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect ap0 ap1 fuel s).1
  (fun out=>TraceLog ap0 ap1 fuel s (collect ap0 ap1 fuel s).2 out ∧ canonical out) := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
  by_cases active : s.1.start.val<16
  · obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
    have obs := NIW_AlignLowExecution.observed ap0 ap1 h0 h1 s.1.start active s.2 hc
    cases call : NIW_AlignLowExecution.step ap0 ap1 s.1.start s.2 with
    | fail err => simp only [call,NIW_AlignFieldReply.Produced] at obs
    | div => simp only [call,NIW_AlignFieldReply.Produced] at obs
    | ok value =>
     rcases value with ⟨after,log⟩
     simp only [call,NIW_AlignFieldReply.Produced] at obs
     have tail := ih (rest,after) (by simpa only [he] using last)
      (by change rest.start.val≤16;omega) obs.2.2.2
      (by change 16-rest.start.val<fuel;omega)
     cases result : (collect ap0 ap1 fuel (rest,after)).1 with
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
end AspisR1.NIW_AlignLowTraceLog
