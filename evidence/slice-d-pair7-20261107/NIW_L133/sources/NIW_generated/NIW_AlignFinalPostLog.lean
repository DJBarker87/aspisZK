import NIW_AlignFinalTraceLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinalPostLog
open Aeneas Aeneas.Std Result NIT_Cuts NIW_AlignFinalCollect NIW_AlignFinalTraceLog

def post (before : E) : List Event → Result E
 | [] => ok before
 | event::rest => match event.outcome with
   | fail err => fail err
   | div => div
   | ok (after,_) => post after rest

/-- Full post-state reconstruction from the actual chronological event list. -/
theorem traced (parts powers : Parts) (fuel : Nat) (s : NHX_FinalLoop.State)
 (events : List Event) (out : E) (trace : TraceLog parts powers fuel s events out) :
 post s.2 events=ok out := by
 induction trace with
 | done fuel s stop => rfl
 | step fuel s out after log events last cut law scale rest next tail ih =>
  simpa only [post] using ih

theorem source (parts powers : Parts) (h0 : canonical parts) (h1 : canonical powers) (fuel : Nat)
 (s : NHX_FinalLoop.State) (last : s.1.end.val=7) (bound : s.1.start.val≤7)
 (hc : canonE s.2) (enough : 7-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect parts powers fuel s).1
  (fun out=>post s.2 (collect parts powers fuel s).2=ok out) := by
 have observed := NIW_AlignFinalTraceLog.collected parts powers h0 h1 fuel s last bound hc enough
 cases result : (collect parts powers fuel s).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | div => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | ok out =>
  simp only [result,NIW_AlignFieldReply.Produced] at observed ⊢
  exact traced parts powers fuel s _ out observed.1

#print axioms traced
#print axioms source
end AspisR1.NIW_AlignFinalPostLog
