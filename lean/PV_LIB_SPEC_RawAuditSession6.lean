import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_NativeRuntime, `PV_LIB_SPEC_ResourceHistory, `PV_LIB_SPEC_ConcreteCaptures, `PV_LIB_SPEC_ConcreteEntry, `PV_LIB_SPEC_BoundRuntime, `PV_LIB_SPEC_HistoryInvariant, `PV_LIB_SPEC_JointPremises, `PV_LIB_SPEC_ControlRuntime, `PV_LIB_SPEC_ControlHistory, `PV_LIB_SPEC_ControlJoint],
     #[`PV_LIB_SPEC_NativeRuntime.ABI, `PV_LIB_SPEC_NativeRuntime.pureValue, `PV_LIB_SPEC_NativeRuntime.values, `PV_LIB_SPEC_NativeRuntime.native, `PV_LIB_SPEC_NativeRuntime.invalidPure, `PV_LIB_SPEC_NativeRuntime.machineAt, `PV_LIB_SPEC_NativeRuntime.step, `PV_LIB_SPEC_NativeRuntime.GhostFrame, `PV_LIB_SPEC_NativeRuntime.backend_framed, `PV_LIB_SPEC_ResourceHistory.Issued, `PV_LIB_SPEC_ResourceHistory.Context, `PV_LIB_SPEC_ResourceHistory.Execution, `PV_LIB_SPEC_ResourceHistory.arguments, `PV_LIB_SPEC_ResourceHistory.issuing, `PV_LIB_SPEC_ResourceHistory.recordIssue, `PV_LIB_SPEC_ResourceHistory.ordinary, `PV_LIB_SPEC_ResourceHistory.context, `PV_LIB_SPEC_ResourceHistory.request, `PV_LIB_SPEC_ResourceHistory.allocationResources, `PV_LIB_SPEC_ResourceHistory.reservationResources, `PV_LIB_SPEC_ResourceHistory.allocation_binding, `PV_LIB_SPEC_ResourceHistory.reservation_binding, `PV_LIB_SPEC_ResourceHistory.step, `PV_LIB_SPEC_ResourceHistory.run, `PV_LIB_SPEC_ResourceHistory.initial, `PV_LIB_SPEC_ResourceHistory.HistoryAdequacy, `PV_LIB_SPEC_ConcreteCaptures.site, `PV_LIB_SPEC_ConcreteCaptures.zero, `PV_LIB_SPEC_ConcreteCaptures.one, `PV_LIB_SPEC_ConcreteCaptures.captures, `PV_LIB_SPEC_ConcreteCaptures.places, `PV_LIB_SPEC_ConcreteCaptures.runHeader, `PV_LIB_SPEC_ConcreteCaptures.nHeader, `PV_LIB_SPEC_ConcreteCaptures.fHeader, `PV_LIB_SPEC_ConcreteCaptures.taskHeader, `PV_LIB_SPEC_ConcreteCaptures.bytes, `PV_LIB_SPEC_ConcreteCaptures.state, `PV_LIB_SPEC_ConcreteCaptures.receivers, `PV_LIB_SPEC_ConcreteCaptures.run_bytes, `PV_LIB_SPEC_ConcreteCaptures.n_bytes, `PV_LIB_SPEC_ConcreteCaptures.run_typed, `PV_LIB_SPEC_ConcreteCaptures.n_typed, `PV_LIB_SPEC_ConcreteCaptures.f_typed, `PV_LIB_SPEC_ConcreteCaptures.tasks_typed, `PV_LIB_SPEC_ConcreteCaptures.closure, `PV_LIB_SPEC_ConcreteCaptures.entry_nonempty, `PV_LIB_SPEC_ConcreteEntry.primitives, `PV_LIB_SPEC_ConcreteEntry.resources, `PV_LIB_SPEC_ConcreteEntry.environment, `PV_LIB_SPEC_ConcreteEntry.parameters, `PV_LIB_SPEC_ConcreteEntry.store, `PV_LIB_SPEC_ConcreteEntry.input, `PV_LIB_SPEC_ConcreteEntry.fresh, `PV_LIB_SPEC_ConcreteEntry.owner, `PV_LIB_SPEC_ConcreteEntry.validity, `PV_LIB_SPEC_ConcreteEntry.reference, `PV_LIB_SPEC_ConcreteEntry.Value, `PV_LIB_SPEC_ConcreteEntry.fields, `PV_LIB_SPEC_ConcreteEntry.dereference, `PV_LIB_SPEC_ConcreteEntry.reachable, `PV_LIB_SPEC_ConcreteEntry.references, `PV_LIB_SPEC_ConcreteEntry.numbered, `PV_LIB_SPEC_ConcreteEntry.pre, `PV_LIB_SPEC_ConcreteEntry.machine, `PV_LIB_SPEC_ConcreteEntry.joint, `PV_LIB_SPEC_BoundRuntime.allocationToken, `PV_LIB_SPEC_BoundRuntime.frameReply, `PV_LIB_SPEC_BoundRuntime.ordinary_framed, `PV_LIB_SPEC_BoundRuntime.arc, `PV_LIB_SPEC_BoundRuntime.answer, `PV_LIB_SPEC_BoundRuntime.handler, `PV_LIB_SPEC_BoundRuntime.step, `PV_LIB_SPEC_BoundRuntime.run, `PV_LIB_SPEC_BoundRuntime.Machine, `PV_LIB_SPEC_BoundRuntime.source, `PV_LIB_SPEC_BoundRuntime.MachineSpec, `PV_LIB_SPEC_BoundRuntime.execute, `PV_LIB_SPEC_HistoryInvariant.Invariant, `PV_LIB_SPEC_HistoryInvariant.record_mono, `PV_LIB_SPEC_HistoryInvariant.context_origin, `PV_LIB_SPEC_HistoryInvariant.append_record, `PV_LIB_SPEC_HistoryInvariant.step, `PV_LIB_SPEC_HistoryInvariant.initial, `PV_LIB_SPEC_HistoryInvariant.run, `PV_LIB_SPEC_HistoryInvariant.original, `PV_LIB_SPEC_JointPremises.NativeFacets, `PV_LIB_SPEC_JointPremises.nativeFacets, `PV_LIB_SPEC_JointPremises.EntryMachinePremises, `PV_LIB_SPEC_JointPremises.entryMachine, `PV_LIB_SPEC_JointPremises.TableRequirement, `PV_LIB_SPEC_JointPremises.withTable, `PV_LIB_SPEC_ControlRuntime.ordinary, `PV_LIB_SPEC_ControlRuntime.issuing, `PV_LIB_SPEC_ControlRuntime.recordIssue, `PV_LIB_SPEC_ControlRuntime.controlStep, `PV_LIB_SPEC_ControlRuntime.step, `PV_LIB_SPEC_ControlRuntime.run, `PV_LIB_SPEC_ControlRuntime.Machine, `PV_LIB_SPEC_ControlRuntime.source, `PV_LIB_SPEC_ControlRuntime.MachineSpec, `PV_LIB_SPEC_ControlRuntime.execute, `PV_LIB_SPEC_ControlHistory.Invariant, `PV_LIB_SPEC_ControlHistory.record_mono, `PV_LIB_SPEC_ControlHistory.context_origin, `PV_LIB_SPEC_ControlHistory.append_record, `PV_LIB_SPEC_ControlHistory.step, `PV_LIB_SPEC_ControlHistory.initial, `PV_LIB_SPEC_ControlHistory.run, `PV_LIB_SPEC_ControlHistory.original, `PV_LIB_SPEC_ControlJoint.NativeFacets, `PV_LIB_SPEC_ControlJoint.nativeFacets, `PV_LIB_SPEC_ControlJoint.EntryMachinePremises, `PV_LIB_SPEC_ControlJoint.entryMachine, `PV_LIB_SPEC_ControlJoint.TableRequirement, `PV_LIB_SPEC_ControlJoint.withTable])
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
        let stem := "NEP_" ++ mode ++ "_" ++ root.toString
        let mut legacyError := false
        try
          NEP.audit root stem
        catch e =>
          if (← e.toMessageData.toString) != "raw graph disagrees with collectAxioms" then
            throw e
          legacyError := true
        let reached := (← liftIO <| IO.FS.readFile (stem ++ "_REACHABLE.txt")).splitOn "\n"
        let mut reported := (← collectAxioms root).toList
        let mut auxiliaries : Array String := #[]
        let importedEnv := (← getEnv).setExporting false
        let constructors := importedEnv.constants.toList.filterMap fun (n, info) =>
          match info with
          | .ctorInfo _ => if reached.contains n.toString then some n else none
          | _ => none
        for aux in constructors do
          if reached.contains aux.toString then
            elabCommand (← `(command| #print axioms $(mkIdent aux)))
            reported := reported ++ (← collectAxioms aux).toList
            auxiliaries := auxiliaries.push aux.toString
        let summary := (reported.eraseDups.map Name.toString).toArray.qsort (· < ·)
        let env := (← getEnv).setExporting false
        -- Read only the already retained leaf names. No traversal or edge rule changes.
        let mut raw : Array String := #[]
        for n in reached do
          if !n.isEmpty then
            let info ← match env.checked.get.find? n.toName with
              | some info => pure info
              | none =>
                -- Name.toString is not inverted by String.toName for hygienic
                -- numeric components. Resolve uniquely against actual kernel names.
                match env.constants.toList.filter (fun pair => pair.1.toString == n) with
                | [(actual, _)] =>
                  let some found := env.checked.get.find? actual |
                    throwError "unresolved retained constant {n} after unique-name resolution"
                  logInfo m!"NEP63_NAME_RESOLVED {n}"
                  pure found
                | _ => throwError "unresolved or ambiguous retained constant {n}"
            if info.isAxiom then raw := raw.push n
        let rawSorted := raw.qsort (· < ·)
        let equal := rawSorted == summary
        logInfo m!"NEP62_RESULT {(Json.mkObj [("root",toJson root.toString),
          ("auxiliaries",toJson auxiliaries),("summary_axioms",toJson summary),
          ("walked_axioms",toJson rawSorted),("equal",toJson equal),
          ("legacy_root_only_mismatch",toJson legacyError)]).compress}"
        unless equal do throwError "augmented summary disagrees with raw graph"
      catch e =>
        logError e.toMessageData
        failed := true
    return failed
  let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
  match result with
  | .error e =>
    IO.eprintln (← e.toMessageData.toString)
    return 2
  | .ok (failed, state) =>
    for msg in state.messages.toList do IO.println (← msg.data.toString)
    return if failed then 1 else 0

#print axioms main
