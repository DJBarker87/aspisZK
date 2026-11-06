import NKK_ClausesResumeBody
import Lean.Elab.Tactic
set_option autoImplicit false
open Lean Elab Tactic
/-- Syntactic head check avoids speculative unfolding of a long continuation. -/
elab "nkk_close_resume_tail" : tactic => do
 let target ← (← getMainGoal).getType
 unless target.getAppFn.isConstOf ``NKK_LogClauses.Holds do
  throwError "expected a log-clause goal"
 let args := target.getAppArgs
 unless args.size > 0 do throwError "missing source computation"
 let body := args[args.size-1]!
 unless body.getAppFn.isConstOf ``NJU_ResumeObserved.resumeBodyG do
  throwError "not the literal resume body continuation"
 evalTactic (← `(tactic| apply NKK_ResumeClauses.resumeBody))
