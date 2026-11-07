import NMT_345Decoder
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "NFY_NBN_" && (s.splitOn "_proof").length == 1 &&
     (s.splitOn "_simp").length == 1 && (s.splitOn ".eq_").length == 1 then
   match info with
   | .thmInfo d => logInfo m!"{n}: {d.type}"
   | .defnInfo d =>
      if ((s.toLower.splitOn "decode").length > 1) then logInfo m!"DEF {n}: {d.type}"
   | _ => pure ()
