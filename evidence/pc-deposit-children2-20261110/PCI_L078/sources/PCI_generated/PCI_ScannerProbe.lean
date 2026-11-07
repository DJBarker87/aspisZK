import NFY_Part053
open Lean Elab Command
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s:=n.toString
  if s.startsWith "NFY_NED_ScannerCohorts." || s=="NBD_DigestInduction.Canonical" then
   logInfo m!"DEF {s}\nTYPE {ci.type}"
   if s=="NBD_DigestInduction.Canonical" then logInfo m!"VALUE {ci.value? true}"
