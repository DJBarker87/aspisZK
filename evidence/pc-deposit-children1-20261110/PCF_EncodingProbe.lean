import Aeneas
open Lean Elab Command
run_cmd do
  let env ← Lean.getEnv
  for (n,ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Aeneas.Std.core.num.U32.to_le_bytes" ||
       s.startsWith "Aeneas.Std.core.num.U64.to_le_bytes" then
      logInfo m!"FOUND {s}\nTYPE {ci.type}"
      if s == "Aeneas.Std.core.num.U32.to_le_bytes" ||
         s == "Aeneas.Std.core.num.U64.to_le_bytes" then
        logInfo m!"VALUE {ci.value? true}"
