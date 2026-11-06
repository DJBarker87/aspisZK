import NJB_StubLaws
import NFQ_PreparedMultiplier
open Lean Elab Command
#print AspisR1.FIv_NativeValue.zero
#print AspisR1.FIv_PreparedTotal.mul
#check NFQ_PreparedMultiplier.source
run_cmd do
 let env ← getEnv
 for (n, _) in env.constants.toList do
  if n.toString.startsWith "AspisR1.FIv_PreparedNew." then
   elabCommand (← `(command| #check $(mkIdent n)))
