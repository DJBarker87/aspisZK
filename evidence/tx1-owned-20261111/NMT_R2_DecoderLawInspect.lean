import NMT_345Decoder
import NMT_345Encoder
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "NFY_" &&
    ((s.splitOn "result").length > 1 || (s.splitOn "total").length > 1 ||
     (s.splitOn "header").length > 1 || (s.splitOn "decode").length > 1) then
   match info with
   | .thmInfo d => logInfo m!"{n}: {d.type}"
   | _ => pure ()
