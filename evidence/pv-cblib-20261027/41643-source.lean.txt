import Aeneas
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "String." && (s.contains "fromUTF8" || s.contains "toByteArray" || s == "String.ext")) ||
       (s.startsWith "ByteArray." && (s.contains "map" || s.contains "toList")) then
      logInfo m!"{n} : {c.type}"
