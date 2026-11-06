import R0P.Poseidon
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  if n.toString.endsWith ".poseidon_rounds_split" || n.toString.endsWith ".poseidon_compose_steps" then
   logInfo m!"NJE_PRIVATE_REUSE {n} : {c.type}"
