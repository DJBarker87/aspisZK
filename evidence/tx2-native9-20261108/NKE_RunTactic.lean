import Lean
import NKE_RunExt
import NKE_EventTactic
open Lean Elab Tactic
elab "nke_run_bind" : tactic => do
 let goal ← getMainTarget
 unless goal.isAppOf ``Eq do throwError "not an equality"
 let args := goal.getAppArgs
 unless args[1]!.isAppOf ``Bind.bind && args[2]!.isAppOf ``Bind.bind do
  throwError "not two visible writer binds"
 evalTactic (← `(tactic| apply NKE_RunExt.bind))
