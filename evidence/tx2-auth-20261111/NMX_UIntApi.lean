import NMX_BvByte
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  if n.toString.startsWith "UInt64" &&
   ((n.toString.splitOn "shiftRight").length > 1 || (n.toString.splitOn "toUInt8").length > 1) then
   logInfo m!"{n}: {info.type}"
