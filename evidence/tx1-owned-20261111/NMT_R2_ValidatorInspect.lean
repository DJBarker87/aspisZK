import NMT_345Validator
import Lean
open Lean Elab Command
#print NFY_NED_ValidatorTrace.run
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if (s.startsWith "NFY_NBN_StatementResult" || s.startsWith "NFY_NEE_ValidatorGate" ||
      s.startsWith "NFY_NED_ValidatorTrace") &&
      (s.splitOn "_proof").length == 1 && (s.splitOn "_simp").length == 1 then
   match info with
   | .thmInfo d => logInfo m!"{n}: {d.type}"
   | _ => pure ()
