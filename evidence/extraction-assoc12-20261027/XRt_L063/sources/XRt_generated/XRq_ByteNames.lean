import XRo_Join_Installed
open Lean in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  if n.toString.startsWith "BitVec." &&
    (n.toString.toLower.contains "byte" || n.toString.contains "extractLsb") then
   logInfo m!"{n}"
#print BitVec.toLEBytes._unary
