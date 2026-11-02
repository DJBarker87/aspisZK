import R1Z.ProverRwDictionaryBytesSource
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    if (n.toString.splitOn "LEBytes").length > 1 then
      logInfo m!"{n} : {c.type}"
