import NNH_CorrectConfiguration
import LIBC_S1Sources
open Aeneas Aeneas.Std AspisR1
#check AspisS6CurrentCodecInstallation.decode
#check NMT_345.decodeCall
#check NMT_345.validateCall
#check NMT_345.encodeCall
#print AspisS6CurrentCodecInstallation.decode
#print NMT_345Dec.fromT8
open Lean in
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  let s:=n.toString
  if (s.startsWith "NMT_345" || s.startsWith "LIBC_") && (s.splitOn "._").length=1 then
   match info with
   | .thmInfo _ => if (s.splitOn "decode").length>1 || (s.splitOn "total").length>1 || (s.splitOn "native").length>1 then logInfo m!"{n}"
   | _ => pure ()
