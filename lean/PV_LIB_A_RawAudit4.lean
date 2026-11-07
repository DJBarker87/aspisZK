import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_OwnerStore, `PV_LIB_A_OwnerStoreTransport, `PV_LIB_A_WriterSites, `PV_LIB_A_OwnerStoreActions, `PV_LIB_A_RangeWriter, `PV_LIB_A_WriterNumbering, `PV_LIB_A_Caller124, `PV_LIB_A_NameValidity, `PV_LIB_A_PrefixTransport, `PV_LIB_A_WriterOrdinary, `PV_LIB_A_WriterRegistry],
     #[`PV_LIB_A_OwnerStore.agreement, `PV_LIB_A_OwnerStore.installed, `PV_LIB_A_OwnerStore.effects, `PV_LIB_A_OwnerStoreTransport.advance_add, `PV_LIB_A_OwnerStoreTransport.advance_agreement, `PV_LIB_A_OwnerStoreTransport.segment, `PV_LIB_A_OwnerStoreTransport.registry, `PV_LIB_A_WriterSites.source487, `PV_LIB_A_WriterSites.source930, `PV_LIB_A_WriterSites.source3447, `PV_LIB_A_WriterSites.source3519, `PV_LIB_A_WriterSites.source3641, `PV_LIB_A_WriterSites.source3756, `PV_LIB_A_WriterSites.source4327, `PV_LIB_A_WriterSites.source8248, `PV_LIB_A_WriterSites.selected, `PV_LIB_A_WriterSites.installed, `PV_LIB_A_OwnerStoreActions.nonwaiting, `PV_LIB_A_OwnerStoreActions.completed, `PV_LIB_A_RangeWriter.range93, `PV_LIB_A_WriterNumbering.write_counter, `PV_LIB_A_WriterNumbering.local_store, `PV_LIB_A_Caller124.provider_pre, `PV_LIB_A_Caller124.installed, `PV_LIB_A_Caller124.counts, `PV_LIB_A_NameValidity.none_entry, `PV_LIB_A_NameValidity.some_entry, `PV_LIB_A_PrefixTransport.prefix_identity, `PV_LIB_A_WriterOrdinary.noncatch, `PV_LIB_A_WriterOrdinary.installed, `PV_LIB_A_WriterRegistry.installed])
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
