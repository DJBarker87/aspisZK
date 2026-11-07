import NNG_StdFromFn
set_option autoImplicit false
open Lean Elab Command
#print Aeneas.Std.Usize.wrapping_add
#print equations AspisR1.OraclePortStdBuilder.fromFnLoop
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    if n.toString.startsWith "AspisR1.OraclePortStdBuilder" ||
        n.toString.startsWith "Aeneas.Std.Usize.wrapping_add" ||
        n.toString.startsWith "Aeneas.Std.Scalar.wrapping_add" then
      logInfo m!"{n}: {c.type}"
