import NMT_345Decoder
import Lean
open Lean Elab Command
#print NFY_NEX_PublicModel.run
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "NFY_NEX_" || s.startsWith "NFY_NEQ_CommonDecode" || s.startsWith "NFY_NEQ_LateDecode" then
   match info with
   | .defnInfo d => logInfo m!"{n}: {d.type}\n{d.value}"
   | _ => pure ()
