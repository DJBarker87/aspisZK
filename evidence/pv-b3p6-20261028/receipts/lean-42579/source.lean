import Aeneas.Std
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (name.toString.splitOn "toLEBytes").length > 1 then
      logInfo m!"{name}"
