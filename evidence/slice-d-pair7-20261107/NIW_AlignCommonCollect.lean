import NIW_AlignCommonExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignCommonCollect
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_CommonChain

structure Event where
 index : Usize
 before : CommonCells
 outcome : Result (CommonCells×Common)

def collect (w : W) : Nat → NHX_CommonDomain.State → Result (W×CommonCells) × List Event
 | 0,_ => (div,[])
 | fuel+1,s =>
  match core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1 with
  | fail err => (fail err,[])
  | div => (div,[])
  | ok (none,_) => (ok (w,s.2),[])
  | ok (some index,rest) =>
   let call := NIW_AlignCommonExecution.step w index s.2
   let event := Event.mk index s.2 call
   match call with
   | fail err => (fail err,[event])
   | div => (div,[event])
   | ok (after,_) =>
    let tail := collect w fuel (rest,after)
    (tail.1,event::tail.2)

/-- Finite source observation replay constructs the NIT witness at the actual
collected result. It never selects a model log or a different final array. -/
theorem trace (w : W) (hf : NHI_TensorOuterStep.Factors w) (fuel : Nat)
 (s : NHX_CommonDomain.State) (last : s.1.end.val=16) (bound : s.1.start.val≤16)
 (hc : NHI_CellCanon.array s.2) (enough : 16-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect w fuel s).1 (fun out=>Trace w fuel s out) := by
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
      exact .step fuel s out after log last obs.1 obs.2.1 rest next tail
  · have stop : s.1.end.val≤s.1.start.val := by omega
    have next := NHI_ForwardRange.done s.1 stop
    simp only [collect,next,NIW_AlignFieldReply.Produced]
    exact .done fuel s stop

#print axioms trace
end AspisR1.NIW_AlignCommonCollect
