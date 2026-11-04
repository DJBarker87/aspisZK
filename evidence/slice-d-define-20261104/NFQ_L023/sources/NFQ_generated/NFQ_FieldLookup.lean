import NFQ_COMBINED_IMPORT
import Lean
open Lean Elab Command
run_cmd do
  for (n, _) in (← getEnv).constants.toList do
    let s := n.toString
    if s.endsWith ".M31.neg" || s.endsWith ".CM31.from_m31" || s.endsWith ".QM31.from_cm31" then
      logInfo s
