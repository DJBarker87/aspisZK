import R1Z.PV_CBL_FallbackScalar
open Aeneas Aeneas.Std
#print core.num.U32.rotate_right
#print U32.wrapping_shr
#print U32.wrapping_shl
#print U32.wrapping_add
#print UScalar
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Aeneas.Std.UScalar" &&
      (s.contains "rotate" || s.contains "toBitVec" || s.contains "ofBitVec" || s.contains "wrapping_sh") then
      logInfo m!"{n} : {c.type}"
