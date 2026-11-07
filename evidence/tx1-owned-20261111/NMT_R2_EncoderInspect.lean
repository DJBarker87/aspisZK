import NMT_345Encoder
import Lean
open Lean Elab Command
#print NFY_NBN_EncoderSummary.after
#print NFY_NBN_EncoderSummary.after_source
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "AspisR1.S2K.DigestBytes" then
   logInfo m!"{n}: {info.type}"
   match info with
   | .defnInfo d => logInfo m!"{d.value}"
   | _ => pure ()
