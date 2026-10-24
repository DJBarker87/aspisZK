import Port18COHERENCE_Kernel
import Port18COHERENCE_CompatibilityLoad
open Lean in
run_elab do
  let all ← Port18COHERENCE_Load.load
  let selected ← (Port18COHERENCE_Load.select all #[`AspisR1.Port17RELEASE_Invariant.tx1, `AspisR1.Port17RELEASE_Invariant.tx2, `AspisR1.Port17RELEASE_Domain.delegated])
  let env ← getEnv
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  for (n,c) in selected.toList do
    if let some old := env.checked.get.find? n then
      unless Port18COHERENCE_Load.sameDeclaration old c do
        throwError "existing checked declaration differs: {n}"
    else fresh := fresh.insert n c
  logInfo m!"Rechecking {fresh.size} declarations; no project cache imported"
  let checked ← (Port18COHERENCE_Kernel.replay fresh env)
  setEnv checked
  logInfo "Kernel reconstruction succeeded"
