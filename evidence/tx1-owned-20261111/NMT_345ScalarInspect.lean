import NMT_345Carriers
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "Aeneas.Std.UScalar" && ((s.toLower.splitOn "beq").length > 1 || (s.toLower.splitOn "bne").length > 1) then
   logInfo m!"{n}: {info.type}"
   match info with
   | .defnInfo d => logInfo m!"definition: {d.value}"
   | _ => pure ()
