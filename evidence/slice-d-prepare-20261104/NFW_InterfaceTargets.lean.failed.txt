import NFW_STAGE2_IMPORT
import Lean
open Lean Elab Command
/- Inspect the exact unresolved integration statements without normalizing any
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

/- Record the exact loaded cohort caller declarations for the handoff. No
kernel reduction, theorem change or release proof is performed here. -/
run_cmd do
 let env ← getEnv
 let targets := ["candidate.prepare", "candidate.tx1", "candidate.tx2_common",
  "Prepared.new", "r1_semantic.verify_observed", "r1_wire.begin",
  "r1_semantic.public_transcript", "r1_semantic.verify_finish"]
 let mut count := 0
 for i in [:env.header.moduleData.size] do
  let data := env.header.moduleData[i]!
  for c in data.constants do
   let name := c.name.toString
   if (name.startsWith "AspisR1PublicPreparation." || name.startsWith "AspisR1Stage2.") &&
      targets.any (fun suffix => name.endsWith suffix) then
    count := count+1
    logInfo m!"COHORT_CALLER {c.name} OWNER {env.header.moduleNames[i]!} : {c.type}"
 logInfo m!"COHORT_CALLER_COUNT {count}"
 let n := `AspisR1.RPx_Deployed.deployed
 let some c := env.find? n | throwError "Missing authoritative headline {n}"
 logInfo m!"AUTHORITATIVE_HEADLINE {n} : {c.type}"
