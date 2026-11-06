import NJP_CohortWrite
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
   let s := n.toString
   if s.startsWith "Aeneas.Std." &&
       (s.contains ".xor" || s.contains ".and" || s.contains "HXor" || s.contains "HAnd") then
     logInfo m!"NJP_BIT_OP {n} : {c.type} value={c.value? true}"
