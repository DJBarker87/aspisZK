import NNG_EmittedContext
set_option autoImplicit false
open Lean Elab Command
#print Aeneas.Std.UScalar.size
#print Aeneas.Std.UScalarTy.numBits
run_cmd do
  let env ← getEnv
  for (n,c) in env.constants.toList do
    if n.toString.startsWith "Aeneas.Std.UScalar.size" ||
        n.toString.startsWith "Aeneas.Std.UScalarTy" ||
        n.toString.startsWith "Aeneas.Std.Usize.size" then
      match c with
      | .thmInfo _ => logInfo m!"{n}: {c.type}"
      | .axiomInfo _ => logInfo m!"{n}: {c.type}"
      | _ => pure ()
