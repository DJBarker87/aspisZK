import NIW_AlignCommonTraceLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignCommonPostLog
open Aeneas Aeneas.Std Result NIT_Cuts NIW_AlignCommonCollect NIW_AlignCommonTraceLog

def post (before : CommonCells) : List Event → Result CommonCells
 | [] => ok before
 | event::rest => match event.outcome with
   | fail err => fail err
   | div => div
   | ok (after,_) => post after rest

/-- Full post-state reconstruction from the actual chronological event list. -/
theorem traced (w : W) (fuel : Nat) (s : NHX_CommonDomain.State)
 (events : List Event) (out : W×CommonCells) (trace : TraceLog w fuel s events out) :
 post s.2 events=ok out.2 := by
 induction trace with
 | done fuel s stop => rfl
 | step fuel s out after log events last cut law rest next tail ih =>
  simpa only [post] using ih

theorem source (w : W) (hf : NHI_TensorOuterStep.Factors w) (fuel : Nat)
 (s : NHX_CommonDomain.State) (last : s.1.end.val=16) (bound : s.1.start.val≤16)
 (hc : NHI_CellCanon.array s.2) (enough : 16-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect w fuel s).1
  (fun out=>post s.2 (collect w fuel s).2=ok out.2) := by
 have observed := NIW_AlignCommonTraceLog.collected w hf fuel s last bound hc enough
 cases result : (collect w fuel s).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | div => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | ok out =>
  simp only [result,NIW_AlignFieldReply.Produced] at observed ⊢
  exact traced w fuel s _ out observed.1

#print axioms traced
#print axioms source
end AspisR1.NIW_AlignCommonPostLog
