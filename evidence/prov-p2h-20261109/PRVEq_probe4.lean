import Aeneas
import RPu_FIq_Native05
import RPu_FIq_Native07
import RPu_FIq_Native09
import RPu_FIq_Native10
import RPu_FIq_Native11
import RPu_FIq_Native13
import RPu_FIq_CopyPrefix
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in [``FIq_Native.field.QM31.ZERO, ``FIq_Native.field.QM31.ONE, ``FIq_Native.field.M31.ONE, ``FIq_Native.field.M31.ZERO] do
    let m := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
    logInfo m!"{n} defined in {m}"
