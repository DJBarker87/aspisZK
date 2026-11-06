import NIW_AlignLibraTraceLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibraPostLog
open Aeneas Aeneas.Std Result NIT_Cuts NIW_AlignLibraCollect NIW_AlignLibraTraceLog

def post (before : Parts) : List Event → Result Parts
 | [] => ok before
 | event::rest => match event.outcome with
   | fail err => fail err
   | div => div
   | ok (after,_) => post after rest

theorem traced (f : Ref (Slice U8)) (weights : Powers) (fuel : Nat) (s : NIG_LibraLoop.State)
 (events : List Event) (out : Result Parts) (trace : TraceLog f weights fuel s events out) : post s.2 events=out := by
 induction trace with
 | done fuel s stop => rfl
 | failed fuel s err last active field => rfl
 | diverged fuel s last active field => rfl
 | step fuel s out after log events last cut field mulLaw addLaw rest next tail ih =>
  simpa only [post] using ih

/-- Replaying only the actual logged post-states reconstructs the complete
Libra Result, including the entered fail/div prefix with no made-up post. -/
theorem source (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (weights : Powers) (cw : canonical weights) (fuel : Nat) (s : NIG_LibraLoop.State)
 (last : s.1.end.val=4) (bound : s.1.start.val≤4) (cp : canonical s.2) (enough : 4-s.1.start.val<fuel) :
 post s.2 (collect f weights fuel s).2=(collect f weights fuel s).1 :=
 traced f weights fuel s _ _ (NIW_AlignLibraTraceLog.collected f size weights cw fuel s last bound cp enough).1

#print axioms traced
#print axioms source
end AspisR1.NIW_AlignLibraPostLog
