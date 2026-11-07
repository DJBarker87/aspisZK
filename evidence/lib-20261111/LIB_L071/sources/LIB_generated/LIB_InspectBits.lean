import LIB_Carriers
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s := n.toString
  if s.startsWith "BitVec.getLsbD_" || s.startsWith "BitVec.setWidth_" ||
     s.startsWith "BitVec.fromLEBytes_" then
   logInfo m!"{n} : {c.type}"
