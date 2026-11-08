import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SLICE_Spec_f21],
     #[`PV_LIB_SLICE_Spec_f21.Event, `PV_LIB_SLICE_Spec_f21.Machine, `PV_LIB_SLICE_Spec_f21.Entry, `PV_LIB_SLICE_Spec_f21.start, `PV_LIB_SLICE_Spec_f21.execution, `PV_LIB_SLICE_Spec_f21.Pre, `PV_LIB_SLICE_Spec_f21.ResourceRequest, `PV_LIB_SLICE_Spec_f21.Environment, `PV_LIB_SLICE_Spec_f21.MachineSpec, `PV_LIB_SLICE_Spec_f21.Pending, `PV_LIB_SLICE_Spec_f21.Boundary, `PV_LIB_SLICE_Spec_f21.First, `PV_LIB_SLICE_Spec_f21.storeView, `PV_LIB_SLICE_Spec_f21.statusView, `PV_LIB_SLICE_Spec_f21.Observation, `PV_LIB_SLICE_Spec_f21.observe, `PV_LIB_SLICE_Spec_f21.Outcome, `PV_LIB_SLICE_Spec_f21.reference, `PV_LIB_SLICE_Spec_f21.Frame, `PV_LIB_SLICE_Spec_f21.Success, `PV_LIB_SLICE_Spec_f21.SourceFrame, `PV_LIB_SLICE_Spec_f21.encodedLength, `PV_LIB_SLICE_Spec_f21.final_length, `PV_LIB_SLICE_Spec_f21.construction_length, `PV_LIB_SLICE_Spec_f21.package_success_forces_zero, `PV_LIB_SLICE_Spec_f21.Post, `PV_LIB_SLICE_Spec_f21.Contract, `PV_LIB_SLICE_Spec_f21.pre_comparison, `PV_LIB_SLICE_Spec_f21.machine_implies_package, `PV_LIB_SLICE_Spec_f21.pending_implies_old, `PV_LIB_SLICE_Spec_f21.no_false_pending11, `PV_LIB_SLICE_Spec_f21.first_unique, `PV_LIB_SLICE_Spec_f21.abort_prefix])
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
        for aux in #[`PV_LIB_SLICE_Spec_f21.Entry.mk, `PV_LIB_SLICE_Spec_f21.Pre.mk, `PV_LIB_SLICE_Spec_f21.ResourceRequest.mk, `PV_LIB_SLICE_Spec_f21.Environment.mk, `PV_LIB_SLICE_Spec_f21.MachineSpec.mk, `PV_STX2_ToVecCallSummary.Entry.mk, `PV_STX2_ToVecCallSummary.Pre.mk, `PV_STX2_ToVecCallSummary.MachineSpec.mk, `PV_STX2_ToVecCallSummary.Success.mk] do
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
