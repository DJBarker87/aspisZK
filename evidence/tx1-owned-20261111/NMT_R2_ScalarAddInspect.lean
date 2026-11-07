import NMT_345RSLCarriers
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for (n, info) in env.constants.toList do
  let s := n.toString
  if (s.startsWith "Aeneas.Std.UScalar" || s.startsWith "Aeneas.Std.Usize") &&
    ((s.splitOn "add").length > 1 || (s.splitOn "tryMk").length > 1) &&
    (s.splitOn "_proof").length == 1 && (s.splitOn "_simp").length == 1 then
   logInfo m!"{n}: {info.type}"
   if s.endsWith ".add" || s.endsWith ".tryMk" then
    match info with
    | .defnInfo d => logInfo m!"{d.value}"
    | _ => pure ()
#print NGL_DistinctInduction.outer
#print NGL_DistinctInduction.inner
