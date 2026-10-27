import Aeneas
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "Aeneas.Std.U8" || s.startsWith "Aeneas.Std.UScalar") &&
        (s.endsWith "ofNat" || s.endsWith "ofNatCore" || s.endsWith "ofNatClamp" || s.endsWith "ofNatTruncate") ||
        (s.startsWith "String." && (s.endsWith "fromUTF8?" || s.endsWith "toUTF8" || s.endsWith "toByteArray")) then
      logInfo m!"{n} : {c.type}"
#print Aeneas.Std.U8
#print UInt8.toNat_lt
