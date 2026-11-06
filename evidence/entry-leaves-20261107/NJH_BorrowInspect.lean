import NJH_Ref.Funs
import S2TrustedSdkBorrow
run_elab do
  let env ← Lean.getEnv
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.contains "wrapping_add" || s.contains "wrapping_sub") &&
        (s.contains "IScalar" || s.contains "I64") then
      Lean.logInfo m!"{n}"
#print Aeneas.Std.I64.wrapping_add
#print Aeneas.Std.I64.wrapping_sub
