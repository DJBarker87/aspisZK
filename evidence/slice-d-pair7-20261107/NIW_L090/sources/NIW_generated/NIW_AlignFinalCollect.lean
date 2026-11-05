import NIW_AlignFinalExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinalCollect
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

structure Event where
 index : Usize
 before : E
 outcome : Result (E×Final)

def collect (parts powers : Parts) : Nat → NHX_FinalLoop.State → Result E × List Event
 | 0,_ => (div,[])
 | fuel+1,s =>
  match core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1 with
  | fail err => (fail err,[])
  | div => (div,[])
  | ok (none,_) => (ok s.2,[])
  | ok (some index,rest) =>
   let call := NIW_AlignFinalExecution.step parts powers index s.2
   let event := Event.mk index s.2 call
   match call with
   | fail err => (fail err,[event])
   | div => (div,[event])
   | ok (after,_) =>
    let tail := collect parts powers fuel (rest,after)
    (tail.1,event::tail.2)

/-- Finite source observation replay constructs the NIT witness at the actual
collected result. It never selects a model log or a different final array. -/
theorem trace (parts powers : Parts) (h0 : canonical ap0) (h1 : canonical ap1) (fuel : Nat)
 (s : NHX_FinalLoop.State) (last : s.1.end.val=7) (bound : s.1.start.val≤7)
 (hc : canonE s.2) (enough : 7-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect parts powers fuel s).1 (fun out=>FinalTrace parts powers fuel s out ∧ canonE out) := by
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
      exact ⟨.step fuel s out after log obs.1 obs.2.1 obs.2.2.1 rest next tail.1,tail.2⟩
  · have stop : s.1.end.val≤s.1.start.val := by omega
    have next := NHI_ForwardRange.done s.1 stop
    simp only [collect,next,NIW_AlignFieldReply.Produced]
    exact ⟨.done fuel s stop,hc⟩

#print axioms trace
end AspisR1.NIW_AlignFinalCollect
