import NIW_AlignLibraExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibraCollect
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_LibraChain

structure Event where
 index : Usize
 before : Parts
 fieldReply : Result E
 outcome : Result (Parts×LibraLog)

def collect (f : Ref (Slice U8)) (libra : Powers) : Nat → NIG_LibraLoop.State → Result Parts × List Event
 | 0,_ => (div,[])
 | fuel+1,s =>
  match core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1 with
  | fail err => (fail err,[])
  | div => (div,[])
  | ok (none,_) => (ok s.2,[])
  | ok (some index,rest) =>
   let read := FIo_Native.weights.field f.value index
   let call := NIW_AlignLibraExecution.afterRead f libra index s.2 read
   let event := Event.mk index s.2 read call
   match call with
   | fail err => (fail err,[event])
   | div => (div,[event])
   | ok (after,_) =>
    let tail := collect f libra fuel (rest,after)
    (tail.1,event::tail.2)

/-- The actual field call decides whether arithmetic and later iterations are
entered. Aborting reads retain their event and no suffix; every returning
step uses its actual field, product, sum and complete mutable Parts. -/
theorem trace (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (libra : Powers) (cl : canonical libra) (fuel : Nat) (s : NIG_LibraLoop.State)
 (last : s.1.end.val=4) (bound : s.1.start.val≤4) (cb : canonical s.2)
 (enough : 4-s.1.start.val<fuel) :
 Trace f libra fuel s (collect f libra fuel s).1 ∧ Post (collect f libra fuel s).1 := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
  by_cases active : s.1.start.val<4
  · obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
    cases field : FIo_Native.weights.field f.value s.1.start with
    | fail err =>
     have call := NIW_AlignLibraExecution.failed f libra s.1.start s.2 err field
     dsimp only [NIW_AlignLibraExecution.step] at call
     simp only [collect,next,call]
     exact ⟨.failed fuel s err last active field,True.intro⟩
    | div =>
     have call := NIW_AlignLibraExecution.diverged f libra s.1.start s.2 field
     dsimp only [NIW_AlignLibraExecution.step] at call
     simp only [collect,next,call]
     exact ⟨.diverged fuel s last active field,True.intro⟩
    | ok coefficient =>
     have obs := NIW_AlignLibraExecution.observed f size libra cl s.1.start active s.2 cb coefficient field
     cases call : NIW_AlignLibraExecution.step f libra s.1.start s.2 with
     | fail err => simp only [call,NIW_AlignFieldReply.Produced] at obs
     | div => simp only [call,NIW_AlignFieldReply.Produced] at obs
     | ok value =>
      rcases value with ⟨after,log⟩
      simp only [call,NIW_AlignFieldReply.Produced] at obs
      have nativeField : FIo_Native.weights.field f.value s.1.start=ok log.coefficient := by
       rw [obs.2.1];exact field
      have tail := ih (rest,after) (by simpa only [he] using last)
       (by change rest.start.val≤4;omega) obs.2.2.2.2
       (by change 4-rest.start.val<fuel;omega)
      dsimp only [NIW_AlignLibraExecution.step] at call
      simp only [collect,next,call]
      exact ⟨.step fuel s _ after log last obs.1 nativeField obs.2.2.1 obs.2.2.2.1 rest next tail.1,tail.2⟩
  · have stop : s.1.end.val≤s.1.start.val := by omega
    have next := NHI_ForwardRange.done s.1 stop
    simp only [collect,next]
    exact ⟨.done fuel s stop,cb⟩

#print axioms trace
end AspisR1.NIW_AlignLibraCollect
