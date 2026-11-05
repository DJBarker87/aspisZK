import NIW_AlignLibraCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibraTraceLog
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIW_AlignLibraCollect

inductive TraceLog (f : Ref (Slice U8)) (weights : Powers) :
 Nat → NIG_LibraLoop.State → List Event → Result Parts → Prop
 | done (fuel : Nat) (s : NIG_LibraLoop.State) (stop : s.1.end.val≤s.1.start.val) :
   TraceLog f weights (fuel+1) s [] (ok s.2)
 | failed (fuel : Nat) (s : NIG_LibraLoop.State) (err : Error)
   (last : s.1.end.val=4) (active : s.1.start.val<4)
   (field : FIo_Native.weights.field f.value s.1.start=fail err) :
   TraceLog f weights (fuel+1) s [⟨s.1.start,s.2,FIo_Native.weights.field f.value s.1.start,fail err⟩] (fail err)
 | diverged (fuel : Nat) (s : NIG_LibraLoop.State)
   (last : s.1.end.val=4) (active : s.1.start.val<4)
   (field : FIo_Native.weights.field f.value s.1.start=div) :
   TraceLog f weights (fuel+1) s [⟨s.1.start,s.2,FIo_Native.weights.field f.value s.1.start,div⟩] div
 | step (fuel : Nat) (s : NIG_LibraLoop.State) (out : Result Parts) (after : Parts)
   (log : LibraLog) (events : List Event) (last : s.1.end.val=4)
   (cut : cutLibraLog f weights s.1.start.val s.2 log after)
   (field : FIo_Native.weights.field f.value s.1.start=ok log.coefficient)
   (mulLaw : EMul log.mul_a log.mul_b log.product) (addLaw : EAdd log.add_a log.add_b log.reply)
   (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : TraceLog f weights fuel (rest,after) events out) :
   TraceLog f weights (fuel+1) s
    (⟨s.1.start,s.2,FIo_Native.weights.field f.value s.1.start,ok (after,log)⟩::events) out

theorem forget (f : Ref (Slice U8)) (weights : Powers) (fuel : Nat) (s : NIG_LibraLoop.State)
 (events : List Event) (out : Result Parts) (trace : TraceLog f weights fuel s events out) :
 NIT_LibraChain.Trace f weights fuel s out := by
 induction trace with
 | done fuel s stop => exact .done fuel s stop
 | failed fuel s err last active field => exact .failed fuel s err last active field
 | diverged fuel s last active field => exact .diverged fuel s last active field
 | step fuel s out after log events last cut field mulLaw addLaw rest next tail ih =>
  exact .step fuel s out after log last cut field mulLaw addLaw rest next ih

theorem collected (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (weights : Powers) (cw : canonical weights) (fuel : Nat) (s : NIG_LibraLoop.State)
 (last : s.1.end.val=4) (bound : s.1.start.val≤4) (cp : canonical s.2) (enough : 4-s.1.start.val<fuel) :
 TraceLog f weights fuel s (collect f weights fuel s).2 (collect f weights fuel s).1 ∧
 NIT_LibraChain.Post (collect f weights fuel s).1 := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
  by_cases active : s.1.start.val<4
  · obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
    cases field : FIo_Native.weights.field f.value s.1.start with
    | fail err =>
     have call := NIW_AlignLibraExecution.failed f weights s.1.start s.2 err field
     dsimp only [NIW_AlignLibraExecution.step] at call
     simp only [collect,next,call]
     exact ⟨.failed fuel s err last active field,True.intro⟩
    | div =>
     have call := NIW_AlignLibraExecution.diverged f weights s.1.start s.2 field
     dsimp only [NIW_AlignLibraExecution.step] at call
     simp only [collect,next,call]
     exact ⟨.diverged fuel s last active field,True.intro⟩
    | ok coefficient =>
     have obs := NIW_AlignLibraExecution.observed f size weights cw s.1.start active s.2 cp coefficient field
     cases call : NIW_AlignLibraExecution.step f weights s.1.start s.2 with
     | fail err => simp only [call,NIW_AlignFieldReply.Produced] at obs
     | div => simp only [call,NIW_AlignFieldReply.Produced] at obs
     | ok value =>
      rcases value with ⟨after,log⟩
      simp only [call,NIW_AlignFieldReply.Produced] at obs
      have hf : FIo_Native.weights.field f.value s.1.start=ok log.coefficient := by rw [obs.2.1];exact field
      have tail := ih (rest,after) (by simpa only [he] using last)
       (by change rest.start.val≤4;omega) obs.2.2.2.2 (by change 4-rest.start.val<fuel;omega)
      dsimp only [NIW_AlignLibraExecution.step] at call
      simp only [collect,next,call]
      exact ⟨.step fuel s _ after log _ last obs.1 hf obs.2.2.1 obs.2.2.2.1 rest next tail.1,tail.2⟩
  · have stop : s.1.end.val≤s.1.start.val := by omega
    have next := NHI_ForwardRange.done s.1 stop
    simp only [collect,next]
    exact ⟨.done fuel s stop,cp⟩

#print axioms forget
#print axioms collected
end AspisR1.NIW_AlignLibraTraceLog
