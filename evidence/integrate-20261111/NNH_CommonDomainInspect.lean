import NNH_064Install
open AspisR1
#print NID_ResumeFields.Domain
open Lean in
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  let s := n.toString
  if (s.startsWith "NKO_C07" || s.startsWith "NID_ResumeFields" || s.startsWith "NHT_QueryTail") && (s.splitOn "._").length=1 then
   match info with
   | .thmInfo _ => logInfo m!"{n}"
   | _ => pure ()
