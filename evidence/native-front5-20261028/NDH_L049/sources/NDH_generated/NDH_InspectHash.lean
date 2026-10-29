import R1Merkle32Leaf
import NDH_TranscriptReference.Funs
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let text := name.toString
    if text.startsWith "List.ofFn" || text.endsWith "CopyUnit" then
      logInfo m!"{name}: {info.type}"
