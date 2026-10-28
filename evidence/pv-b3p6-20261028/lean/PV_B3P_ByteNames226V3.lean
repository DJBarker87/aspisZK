import Aeneas.Std
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if "toLEBytes".isInfixOf name.toString then
      logInfo m!"{name}"
