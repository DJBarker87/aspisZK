import R1Z.ProverRwFullExternalFuns
open Lean Elab Command
/- Focused inventory of owned-string adapters missed by the alloc namespace
filter in LibraryAPI. No callback assumption or source-law claim. -/
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Aeneas.Std.String" || s.startsWith "alloc.string." ||
       (s.startsWith "String." &&
        (s.endsWith "fromUTF8?" || s.endsWith "toUTF8" ||
         s.endsWith "append" || s.endsWith "empty")) then
      logInfo m!"{n} : {c.type}"
#print String
#print Aeneas.Std.Str
