import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_ToVec, `PV_LIB_SPEC_Source7Entry],
     #[`PV_LIB_SPEC_ToVec.Old.Machine, `PV_LIB_SPEC_ToVec.Old.Entry, `PV_LIB_SPEC_ToVec.Event, `PV_LIB_SPEC_ToVec.Machine, `PV_LIB_SPEC_ToVec.Entry, `PV_LIB_SPEC_ToVec.Pre, `PV_LIB_SPEC_ToVec.MachineSpec, `PV_LIB_SPEC_ToVec.execution, `PV_LIB_SPEC_ToVec.start, `PV_LIB_SPEC_ToVec.Pending, `PV_LIB_SPEC_ToVec.Boundary, `PV_LIB_SPEC_ToVec.First, `PV_LIB_SPEC_ToVec.storeView, `PV_LIB_SPEC_ToVec.statusView, `PV_LIB_SPEC_ToVec.Observation, `PV_LIB_SPEC_ToVec.observe, `PV_LIB_SPEC_ToVec.Outcome, `PV_LIB_SPEC_ToVec.reference, `PV_LIB_SPEC_ToVec.Frame, `PV_LIB_SPEC_ToVec.Post, `PV_LIB_SPEC_ToVec.Contract, `PV_LIB_SPEC_ToVec.pre_same, `PV_LIB_SPEC_ToVec.pending_implies_old, `PV_LIB_SPEC_ToVec.no_false_pending11, `PV_LIB_SPEC_ToVec.first_unique, `PV_LIB_SPEC_ToVec.abort_prefix, `PV_LIB_SPEC_Source7Entry.column, `PV_LIB_SPEC_Source7Entry.foundation, `PV_LIB_SPEC_Source7Entry.shape, `PV_LIB_SPEC_Source7Entry.header, `PV_LIB_SPEC_Source7Entry.source, `PV_LIB_SPEC_Source7Entry.state, `PV_LIB_SPEC_Source7Entry.values_empty, `PV_LIB_SPEC_Source7Entry.receiver_source, `PV_LIB_SPEC_Source7Entry.typed_source, `PV_LIB_SPEC_Source7Entry.owned, `PV_LIB_SPEC_Source7Entry.chosen_header, `PV_LIB_SPEC_Source7Entry.identity_zero, `PV_LIB_SPEC_Source7Entry.identities, `PV_LIB_SPEC_Source7Entry.indexed, `PV_LIB_SPEC_Source7Entry.aligned, `PV_LIB_SPEC_Source7Entry.valid, `PV_LIB_SPEC_Source7Entry.owner_wellFormed, `PV_LIB_SPEC_Source7Entry.entry_nonempty, `PV_LIB_SPEC_Source7Entry.store, `PV_LIB_SPEC_Source7Entry.toVecEntry, `PV_LIB_SPEC_Source7Entry.toVec_pre, `PV_LIB_SPEC_Source7Entry.toVec_entry_nonempty])
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
