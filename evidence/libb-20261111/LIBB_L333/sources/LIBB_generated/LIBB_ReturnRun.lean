import LIBB_ReturnTrace
set_option autoImplicit false
noncomputable section
namespace LIBB_ReturnRun
open Aeneas Aeneas.Std AspisR1 VTop_Stages NJU_CommonObserved LIBB_ReturnTrace
open Lean Elab Tactic Meta
/-- Dispatch only on the visible source log constructor. Never unfold child calls. -/
elab "safe_step" : tactic => do
 let g ← getMainGoal
 let t ← g.getType
 if t.isForall then
  evalTactic (← `(tactic| intro x))
 else
  let args := t.getAppArgs
  unless t.isAppOf ``LIBB_ReturnTrace.Safe do throwError "not Safe"
  let m := args[1]!
  if m.isAppOf ``Bind.bind then
   evalTactic (← `(tactic| apply LIBB_ReturnTrace.bind))
  else if m.isAppOf ``NJU_Log.record then
   evalTactic (← `(tactic| apply LIBB_ReturnTrace.record; intro a pr p folded err equal; cases equal))
  else if m.isAppOf ``liftM || m.isAppOf ``MonadLift.monadLift then
   evalTactic (← `(tactic| exact LIBB_ReturnTrace.lift _))
  else if m.isAppOf ``Pure.pure then
   evalTactic (← `(tactic| exact LIBB_ReturnTrace.pure _))
  else if m.isLet || m.isAppOf ``Prod.casesOn then
   evalTactic (← `(tactic| dsimp only [NJU_Log.prod_cases]))
  else
   evalTactic (← `(tactic| split))

theorem run (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 Safe (NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none) := by
 unfold NJU_CommonObserved.run
 safe_step
 safe_step
 trace_state

#print axioms run
end LIBB_ReturnRun
end
