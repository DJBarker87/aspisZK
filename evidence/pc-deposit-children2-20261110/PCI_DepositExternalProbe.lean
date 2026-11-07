import NFY_Part005
import PCF_ResultAssoc
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s := n.toString
  if s.endsWith ".ok_or" || s.endsWith ".CoreCmpPartialEqArray.ne" || s.endsWith ".CoreCmpPartialEqSlice.eq" then
   logInfo m!"FOUND {n}: {c.type}"
