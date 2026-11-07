import NMX_BvByte
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  if (n.toString.splitOn "toLEBytes").length > 1 then
   logInfo m!"{n}: {info.type}"
