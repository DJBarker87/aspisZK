import Lean
import S2StdAnySourceTotalV1
open Lean Elab Command
run_elab do
 let env := (← getEnv).setExporting false
 for entry in env.constants.toList do
  let n := entry.1
  if n.toString.endsWith "anyLoop_unfold" then
   logInfo m!"{n.toString}"
