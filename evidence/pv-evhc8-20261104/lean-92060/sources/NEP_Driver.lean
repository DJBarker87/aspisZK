import Lean
namespace NEP
/-- Raw checked-kernel graph. No imported axiom summaries enter the traversal. -/
def audit (root : Name) (stem : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let mut pending := #[(root, root)]
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut axioms : Array String := #[]
  let mut edges := 0
  while !pending.isEmpty do
    let (n, parent) := pending.back!
    pending := pending.pop
    let some c := env.checked.get.find? n | do
      logInfo m!"NEP_FAILURE {(Json.mkObj [("root", toJson root.toString),
        ("missing", toJson n.toString), ("parent", toJson parent.toString),
        ("discovered_constants_before_failure", toJson seen.size),
        ("edges_scanned_before_failure", toJson edges),
        ("complete", toJson false)]).compress}"
      throwError "missing reachable constant {n}; parent {parent}; visited {seen.size}"
    if c.isAxiom then axioms := axioms.push n.toString
    let mut refs := c.type.getUsedConstants ++
      ((c.value? true).map Expr.getUsedConstants).getD #[]
    if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
    edges := edges + refs.size
    for dep in refs do
      if !seen.contains dep then
        seen := seen.insert dep
        pending := pending.push (dep, n)
  let reached := seen.toArray.qsort Name.lt
  liftIO <| IO.FS.writeFile (stem ++ "_REACHABLE.txt")
    (String.intercalate "\n" (reached.toList.map Name.toString) ++ "\n")
  let walked := axioms.qsort (· < ·)
  let reported := ((← collectAxioms root).map Name.toString).qsort (· < ·)
  logInfo m!"NEP_RESULT {(Json.mkObj [("root", toJson root.toString),
    ("reachable_constants", toJson reached.size), ("edges_scanned", toJson edges),
    ("walked_axioms", toJson walked), ("collect_axioms", toJson reported),
    ("equal", toJson (walked == reported))]).compress}"
  unless walked == reported do throwError "raw graph disagrees with collectAxioms"
-- Private-data loading belongs in the standalone NEP_Driver runtime. Dynamic
-- initializer execution must not be nested in an existing elaborator environment.
end NEP

open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "combined"
  let modules := #[`RPx_Deployed, `PV_BR_FixtureConsumer]
  let roots := #[`PV_EVH_FixtureConsumer.deployedInstance, `PV_EVH_FixtureConsumer.instance_nonvacuity, `PV_EVH_FixtureConsumer.public_fibre, `PV_EVH_FixtureConsumer.two_transaction_nonvacuity, `PV_BR_Transport.payment_left_inverse, `PV_BR_Transport.payment_right_inverse, `PV_BR_Transport.payment_discriminant, `PV_BR_Transport.payment_injective, `PV_BR_Transport.tree_left_inverse, `PV_BR_Transport.tree_right_inverse, `PV_BR_Transport.tree_discriminant, `PV_BR_Transport.tree_injective, `PV_BR_Transport.verifier_retraction, `PV_BR_Transport.verifier_join_split, `PV_BR_Transport.verifier_split_join, `PV_BR_Transport.verifier_embedding_injective, `PV_BR_Transport.verifier_discriminant, `PV_BR_Transport.mapCoreError_inverse, `PV_BR_Transport.payment_result_transport, `PV_BR_Transport.tree_result_transport, `PV_BR_AdmissionTransport.prover_run_roundtrip, `PV_BR_AdmissionTransport.from_to, `PV_BR_AdmissionTransport.to_from, `PV_BR_AdmissionTransport.mapRunError_inverse, `PV_BR_AdmissionTransport.mapRunError_success, `PV_BR_AdmissionTransport.validateCommon_roundtrip, `PV_BR_AdmissionTransport.validateCommon_success, `R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed, `R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events, `R1Z.PV_RJ4IDB_CallerLive.caller_witness, `AspisR1.NDR_CombinedAudit.sourceOnHeadline, `AspisR1.RPx_Deployed.deployed]
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  let ctx : Command.Context := {
    fileName := "NEP_Driver"
    fileMap := FileMap.ofString ""
    snap? := none
    cancelTk? := none
  }
  let action : CommandElabM Bool := do
    let mut failed := false
    for root in roots do
      try
        elabCommand (← `(command| #print axioms $(mkIdent root)))
        NEP.audit root ("NEP_" ++ mode ++ "_" ++ root.toString)
      catch e =>
        logError e.toMessageData
        return true
    return failed
  let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
  match result with
  | .error e =>
    IO.eprintln (← e.toMessageData.toString)
    return 2
  | .ok (failed, state) =>
    for msg in state.messages.toList do IO.println (← msg.data.toString)
    return if failed then 1 else 0
