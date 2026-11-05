import NIW_AlignCommonCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignCommonTraceLog
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_CommonChain NIW_AlignCommonCollect

/-- The witness records exactly which supplied chronological event belongs to
which constructor, including the full mutable before/after arrays. -/
inductive TraceLog (w : W) : Nat → NHX_CommonDomain.State → List Event → W×CommonCells → Prop
 | done (fuel : Nat) (s : NHX_CommonDomain.State) (stop : s.1.end.val≤s.1.start.val) :
   TraceLog w (fuel+1) s [] (w,s.2)
 | step (fuel : Nat) (s : NHX_CommonDomain.State) (out : W×CommonCells)
   (after : CommonCells) (log : Common) (events : List Event) (last : s.1.end.val=16)
   (cut : cutCommon (row2 w) (row3 w) s.1.start.val s.2 log after)
   (law : QMul log.lhs log.rhs log.reply) (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : TraceLog w fuel (rest,after) events out) :
   TraceLog w (fuel+1) s (⟨s.1.start,s.2,ok (after,log)⟩::events) out

theorem forget (w : W) (fuel : Nat) (s : NHX_CommonDomain.State)
 (events : List Event) (out : W×CommonCells) (trace : TraceLog w fuel s events out) :
 NIT_CommonChain.Trace w fuel s out := by
 induction trace with
 | done fuel s stop => exact .done fuel s stop
 | step fuel s out after log events last cut law rest next tail ih =>
  exact .step fuel s out after log last cut law rest next ih

/-- A source stream determines the constructor's exact logs, not just its
final array. No fresh log or endpoint-equality premise is introduced. -/
theorem collected (w : W) (hf : NHI_TensorOuterStep.Factors w) (fuel : Nat)
 (s : NHX_CommonDomain.State) (last : s.1.end.val=16) (bound : s.1.start.val≤16)
 (hc : NHI_CellCanon.array s.2) (enough : 16-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect w fuel s).1
  (fun out=>TraceLog w fuel s (collect w fuel s).2 out ∧ NHI_CellCanon.array out.2) := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
  by_cases active : s.1.start.val<16
  · obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
    have obs := NIW_AlignCommonExecution.observed w hf s.1.start active s.2 hc
    cases call : NIW_AlignCommonExecution.step w s.1.start s.2 with
    | fail err => simp only [call,NIW_AlignFieldReply.Produced] at obs
    | div => simp only [call,NIW_AlignFieldReply.Produced] at obs
    | ok value =>
     rcases value with ⟨after,log⟩
     simp only [call,NIW_AlignFieldReply.Produced] at obs
     have tail := ih (rest,after) (by simpa only [he] using last)
      (by change rest.start.val≤16;omega) obs.2.2
      (by change 16-rest.start.val<fuel;omega)
     cases result : (collect w fuel (rest,after)).1 with
     | fail err => simp only [result,NIW_AlignFieldReply.Produced] at tail
     | div => simp only [result,NIW_AlignFieldReply.Produced] at tail
     | ok out =>
      simp only [result,NIW_AlignFieldReply.Produced] at tail
      simp only [collect,next,call,result,NIW_AlignFieldReply.Produced]
      exact ⟨.step fuel s out after log _ last obs.1 obs.2.1 rest next tail.1,tail.2⟩
  · have stop : s.1.end.val≤s.1.start.val := by omega
    have next := NHI_ForwardRange.done s.1 stop
    simp only [collect,next,NIW_AlignFieldReply.Produced]
    exact ⟨.done fuel s stop,hc⟩

#print axioms forget
#print axioms collected
end AspisR1.NIW_AlignCommonTraceLog
