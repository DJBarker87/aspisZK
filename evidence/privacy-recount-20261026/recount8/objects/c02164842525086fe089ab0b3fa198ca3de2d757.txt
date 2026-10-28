import R1Z.ProverRwFullFuns
set_option autoImplicit false
#print ProverRwFull.aspis_core.field.M31
#print ProverRwFull.aspis_core.field.CM31
#print ProverRwFull.aspis_core.field.QM31

#print ProverRwFull.aspis_core.field.QM31.from_le_bytes
#print ProverRwFull.host_sumcheck.interpolation_accumulate_loop.body
#check Aeneas.Std.UScalar.val
#print Aeneas.Std.Array
#print Aeneas.Std.Array.update
#print Aeneas.Std.Array.set
#print Aeneas.Std.loop
open Lean Elab Command
elab "#join_loop_names" : command => do
  let env ← getEnv
  for entry in env.constants.toList do
    let n := entry.1
    if n.toString.startsWith "Aeneas.Std.loop" then
      logInfo m!"{n}: {entry.2.type}"
#join_loop_names
