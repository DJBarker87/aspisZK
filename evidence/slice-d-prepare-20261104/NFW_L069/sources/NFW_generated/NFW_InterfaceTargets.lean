import NFW_STAGE2_IMPORT
import Lean
open Lean Elab Command
/-- Inspect the exact unresolved integration statements without normalizing any
recurrence or running a duplicate regression. This module adds no theorem. -/
run_cmd do
 let env ← getEnv
 for n in [`AspisR1.NFW_PrepareQuery.tx1, `AspisR1.NFW_QueryResume.tx2,
   `AspisR1.NFW_PreparedControl.source, `AspisR1.NFW_PreparedCalls.calls,
   `AspisR1.NFW_PreparedProducer.scratch, `AspisR1.NFW_ScalarRho.prepared,
   `AspisR1.NFS_QueryLoopRoot.tx1, `AspisR1.NFS_QueryLoopRoot.tx2] do
  let some c := env.find? n | throwError "Missing integration statement {n}"
  logInfo m!"INTEGRATION_TARGET {n} : {c.type}"
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"OWNER {n} := {env.header.moduleNames[i.toNat]!}"
  | none => throwError "Missing owner {n}"
