import Aeneas.Std
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if (name.toString.splitOn "extend_from_slice").length > 1 ||
       (name.toString.splitOn "Vec.push").length > 1 then
      logInfo m!"{name}"
