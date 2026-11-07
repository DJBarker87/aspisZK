import LIB_Carriers
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  let s := n.toString
  if s.startsWith "BitVec.getElem" || s.startsWith "BitVec.eq_of_get" ||
     s.startsWith "BitVec.testBit" then
   logInfo m!"{n} : {c.type}"
