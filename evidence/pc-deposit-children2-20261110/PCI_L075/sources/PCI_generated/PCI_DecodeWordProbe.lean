import NFY_Part005
open Lean Elab Command
run_cmd do
 let env ← Lean.getEnv
 for (n,ci) in env.constants.toList do
  let s:=n.toString
  if ((s.startsWith "NFY_NBP_DecodeWord." || s.startsWith "NFY_NBG_WideBytes.") && !s.contains '✝') then
   logInfo m!"DEF {s}\nTYPE {ci.type}"
   if s.endsWith ".word" || s.endsWith ".limbs" || s.endsWith ".byte" then logInfo m!"VALUE {ci.value? true}"
