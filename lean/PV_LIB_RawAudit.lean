import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_Arc126, `PV_LIB_Arc216, `PV_LIB_Arc222, `PV_LIB_Array11View, `PV_LIB_Array12View, `PV_LIB_Array15View, `PV_LIB_Array23View, `PV_LIB_ArrayInstances, `PV_LIB_Graph, `PV_LIB_LeafObservation, `PV_LIB_Observation, `PV_LIB_PureLeaves, `PV_LIB_Thread164, `PV_LIB_Thread218, `PV_LIB_Thread315, `PV_LIB_ThreadInstances, `PV_LIB_VecNew, `PV_LIB_View],
     #[`PV_LIB_Arc126.internal_reached, `PV_LIB_Arc126.realizes, `PV_LIB_Arc216.internal_reached, `PV_LIB_Arc216.installed, `PV_LIB_Arc222.internal_reached, `PV_LIB_Arc222.realizes, `PV_LIB_Array11View.abort_prefix, `PV_LIB_Array12View.installed, `PV_LIB_Array12View.cells, `PV_LIB_Array15View.installed, `PV_LIB_Array15View.cells, `PV_LIB_Array23View.installed, `PV_LIB_Array23View.cells, `PV_LIB_ArrayInstances.installed12, `PV_LIB_ArrayInstances.installed15, `PV_LIB_ArrayInstances.installed23, `PV_LIB.graph_unique, `PV_LIB.abort_state_free, `PV_LIB.leaf_abort_prefix, `PV_LIB.abort_prefix, `PV_LIB.observe_view, `PV_LIB_PureLeaves.certified217, `PV_LIB_PureLeaves.certified312, `PV_LIB_PureLeaves.certified313, `PV_LIB_PureLeaves.certified320, `PV_LIB_PureLeaves.certified134, `PV_LIB_PureLeaves.certified344, `PV_LIB_Thread164.installed, `PV_LIB_Thread218.installed, `PV_LIB_Thread315.installed, `PV_LIB_ThreadInstances.installed315, `PV_LIB_ThreadInstances.installed218, `PV_LIB_ThreadInstances.installed222, `PV_LIB_ThreadInstances.installed126, `PV_LIB_VecNew.installed, `PV_LIB.store_cells, `PV_LIB.counter_irrelevant, `PV_LIB.world_events])
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
        for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk] do
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
