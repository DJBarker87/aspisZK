import NIW_AlignLowTraceLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLowPostLog
open Aeneas Aeneas.Std Result NIT_Cuts NIW_AlignLowCollect NIW_AlignLowTraceLog

def post (before : LowCells) : List Event → Result LowCells
 | [] => ok before
 | event::rest => match event.outcome with
   | fail err => fail err
   | div => div
   | ok (after,_) => post after rest

/-- Full post-state reconstruction from the actual chronological event list. -/
theorem traced (ap0 ap1 : Powers) (fuel : Nat) (s : NHX_LowDomain.State)
 (events : List Event) (out : LowCells) (trace : TraceLog ap0 ap1 fuel s events out) :
 post s.2 events=ok out := by
 induction trace with
 | done fuel s stop => rfl
 | step fuel s out after log events last cut law scale rest next tail ih =>
  simpa only [post] using ih

theorem source (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1) (fuel : Nat)
 (s : NHX_LowDomain.State) (last : s.1.end.val=16) (bound : s.1.start.val≤16)
 (hc : canonical s.2) (enough : 16-s.1.start.val<fuel) :
 NIW_AlignFieldReply.Produced (collect ap0 ap1 fuel s).1
  (fun out=>post s.2 (collect ap0 ap1 fuel s).2=ok out) := by
 have observed := NIW_AlignLowTraceLog.collected ap0 ap1 h0 h1 fuel s last bound hc enough
 cases result : (collect ap0 ap1 fuel s).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | div => simp only [result,NIW_AlignFieldReply.Produced] at observed
 | ok out =>
  simp only [result,NIW_AlignFieldReply.Produced] at observed ⊢
  exact traced ap0 ap1 fuel s _ out observed.1

#print axioms traced
#print axioms source
end AspisR1.NIW_AlignLowPostLog
