import R1Z.ProverRwFullExternalFuns
open Lean Elab Command

/- Inspect the actual imported builtin string/byte adapters before choosing a
carrier transport. This module introduces no callback assumption. -/
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Aeneas.Std.alloc.string." ||
       s.startsWith "Aeneas.Std.core.str." || s.startsWith "Aeneas.Std.Str." ||
       s == "Aeneas.Std.Str" || s == "Aeneas.Std.U8.ofUInt8" ||
       s == "Aeneas.Std.U8.ofBitVec" then
      logInfo m!"{n} : {c.type}"

#print ProverRwFull.ExternalFuns.op28

#print Aeneas.Std.Str
#check UInt8.toBitVec
#check ByteArray.data
