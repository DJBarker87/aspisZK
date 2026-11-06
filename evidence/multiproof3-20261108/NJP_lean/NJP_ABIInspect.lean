import NJP_ScalarCarrier
import Lean
#print Aeneas.Std.UScalar.size
#print Aeneas.Std.UScalar.numBits
#print Aeneas.Std.UScalar.ofNatCore
#print Aeneas.Std.UScalar.ofNatCore_val_eq
#print Aeneas.Std.Usize
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
   let s := n.toString
   if (s.contains "numBits" && (s.contains "size" || s.contains "Platform")) || s.endsWith "size_eq" then
     logInfo m!"NJP_ABI_FACT {n} : {c.type}"
