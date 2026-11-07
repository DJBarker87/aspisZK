import NNG_StdFromFn
set_option autoImplicit false
open Lean Elab Command
run_cmd do
 for (n,c) in (←getEnv).constants.toList do
  if n.toString.startsWith "Aeneas.Std.Usize.add" || n.toString.startsWith "Aeneas.Std.UScalar.add" then
   logInfo m!"{n}: {c.type}"
