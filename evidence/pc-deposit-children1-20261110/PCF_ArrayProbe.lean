import Aeneas
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n,ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Aeneas.Std.Array." &&
      ((s.splitOn "getElem?").length > 1 || (s.splitOn "index_usize").length > 1) &&
      (s.splitOn "proof").length == 1 then
      logInfo m!"FOUND {s}\nTYPE {ci.type}\nVALUE {ci.value? true}"
