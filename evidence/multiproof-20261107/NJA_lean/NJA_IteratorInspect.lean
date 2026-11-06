import Aeneas
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  if n.toString.contains "Iterator.all" then
   logInfo m!"NJA_ITERATOR {n}: {c.type}"
