import NMT_345Semantic
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if (s.endsWith ".PROOF_BYTES" || s.endsWith ".POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES") &&
   (s.startsWith "AspisR1PublicPreparation" || s.startsWith "AspisR1TerminalDecoder" || s.startsWith "AdapterRw") then
   logInfo m!"{n}: {info.type}"
   match info with
   | .defnInfo d => logInfo m!"{d.value}"
   | .axiomInfo _ => logInfo m!"AXIOM TEMPLATE; do not install"
   | _ => pure ()
