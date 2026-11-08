import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_ActiveAdoption19, `PV_LIB_SPEC_LaneAJoins19, `PV_LIB_SPEC_ActiveNative19, `PV_LIB_SPEC_ActiveBoundary19, `PV_LIB_SPEC_ActiveConsumption19, `PV_LIB_SPEC_ActiveSource19, `PV_LIB_SPEC_ConsumedHistory19, `PV_LIB_SPEC_ActiveCorrection19, `PV_LIB_SPEC_ContextMachine19],
     #[`PV_LIB_SPEC_ActiveAdoption19.step, `PV_LIB_SPEC_ActiveAdoption19.history, `PV_LIB_SPEC_ActiveAdoption19.preserved, `PV_LIB_SPEC_ActiveAdoption19.original85, `PV_LIB_SPEC_ActiveAdoption19.original141, `PV_LIB_SPEC_ActiveAdoption19.world85, `PV_LIB_SPEC_ActiveAdoption19.replies85, `PV_LIB_SPEC_ActiveAdoption19.values_prefix, `PV_LIB_SPEC_ActiveAdoption19.predicate_prefix, `PV_LIB_SPEC_LaneAJoins19.history, `PV_LIB_SPEC_LaneAJoins19.BodyEntry, `PV_LIB_SPEC_LaneAJoins19.OriginalToF6, `PV_LIB_SPEC_LaneAJoins19.RangeEntry, `PV_LIB_SPEC_LaneAJoins19.F6ToRange, `PV_LIB_SPEC_LaneAJoins19.RangeToF361, `PV_LIB_SPEC_LaneAJoins19.F361ToInit, `PV_LIB_SPEC_LaneAJoins19.Joins, `PV_LIB_SPEC_LaneAJoins19.original85, `PV_LIB_SPEC_ActiveNative19.token, `PV_LIB_SPEC_ActiveNative19.request, `PV_LIB_SPEC_ActiveNative19.different, `PV_LIB_SPEC_ActiveNative19.not_tls, `PV_LIB_SPEC_ActiveNative19.trigger, `PV_LIB_SPEC_ActiveNative19.answer, `PV_LIB_SPEC_ActiveBoundary19.changed, `PV_LIB_SPEC_ActiveBoundary19.full, `PV_LIB_SPEC_ActiveBoundary19.successful, `PV_LIB_SPEC_ActiveBoundary19.effects, `PV_LIB_SPEC_ActiveConsumption19.bound, `PV_LIB_SPEC_ActiveConsumption19.delivered, `PV_LIB_SPEC_ActiveConsumption19.consume, `PV_LIB_SPEC_ActiveConsumption19.physical, `PV_LIB_SPEC_ActiveConsumption19.events, `PV_LIB_SPEC_ActiveSource19.store, `PV_LIB_SPEC_ActiveSource19.status, `PV_LIB_SPEC_ActiveSource19.cell, `PV_LIB_SPEC_ActiveSource19.frame, `PV_LIB_SPEC_ConsumedHistory19.step_member, `PV_LIB_SPEC_ConsumedHistory19.run_member, `PV_LIB_SPEC_ConsumedHistory19.poll_consumed, `PV_LIB_SPEC_ConsumedHistory19.prefix_member, `PV_LIB_SPEC_ActiveCorrection19.before, `PV_LIB_SPEC_ActiveCorrection19.after_status, `PV_LIB_SPEC_ActiveCorrection19.nonstall, `PV_LIB_SPEC_ContextMachine19.Machine, `PV_LIB_SPEC_ContextMachine19.Before, `PV_LIB_SPEC_ContextMachine19.run, `PV_LIB_SPEC_ContextMachine19.observe, `PV_LIB_SPEC_ContextMachine19.Behavior, `PV_LIB_SPEC_ContextMachine19.MachineSpec, `PV_LIB_SPEC_ContextMachine19.source, `PV_LIB_SPEC_ContextMachine19.source_spec, `PV_LIB_SPEC_ContextMachine19.run_same, `PV_LIB_SPEC_ContextMachine19.history_same, `PV_LIB_SPEC_ContextMachine19.retained_prefix])
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
