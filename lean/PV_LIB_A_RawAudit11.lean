import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_RangePoll11, `PV_LIB_A_PrefixMachine11, `PV_LIB_A_RangeQuiet11, `PV_LIB_A_RangeStartTrace11, `PV_LIB_A_RangeTailTrace11, `PV_LIB_A_RangeHistory11, `PV_LIB_A_RangeFirst11, `PV_LIB_A_RangeRetry11, `PV_LIB_A_RangeLegacy11, `PV_LIB_A_ChainTrace11, `PV_LIB_A_F6Prefix11, `PV_LIB_A_F6Counter11, `PV_LIB_A_F6Thread11, `PV_LIB_A_F6Panic11, `PV_LIB_A_F6EarlyHistory11, `PV_LIB_A_StoreActionTable11],
     #[`PV_LIB_A_RangePoll11.selected, `PV_LIB_A_RangePoll11.poll, `PV_LIB_A_PrefixMachine11.step, `PV_LIB_A_PrefixMachine11.run, `PV_LIB_A_PrefixMachine11.append, `PV_LIB_A_PrefixMachine11.advance_add, `PV_LIB_A_RangeQuiet11.main5, `PV_LIB_A_RangeQuiet11.main6, `PV_LIB_A_RangeQuiet11.main7, `PV_LIB_A_RangeQuiet11.main8, `PV_LIB_A_RangeQuiet11.main9, `PV_LIB_A_RangeQuiet11.main10, `PV_LIB_A_RangeQuiet11.main11, `PV_LIB_A_RangeQuiet11.main12, `PV_LIB_A_RangeQuiet11.loop0, `PV_LIB_A_RangeQuiet11.loop1, `PV_LIB_A_RangeQuiet11.loop2, `PV_LIB_A_RangeQuiet11.loop3, `PV_LIB_A_RangeQuiet11.loop4, `PV_LIB_A_RangeQuiet11.loop5, `PV_LIB_A_RangeStartTrace11.cons_run, `PV_LIB_A_RangeStartTrace11.wait165, `PV_LIB_A_RangeStartTrace11.storage2, `PV_LIB_A_RangeStartTrace11.call2, `PV_LIB_A_RangeStartTrace11.prefix5, `PV_LIB_A_RangeTailTrace11.move3, `PV_LIB_A_RangeTailTrace11.loop6, `PV_LIB_A_RangeTailTrace11.enter7, `PV_LIB_A_RangeHistory11.prefix_trace, `PV_LIB_A_RangeHistory11.corrected_prefix, `PV_LIB_A_RangeHistory11.poll, `PV_LIB_A_RangeFirst11.cell, `PV_LIB_A_RangeFirst11.history, `PV_LIB_A_RangeFirst11.written, `PV_LIB_A_RangeRetry11.pending, `PV_LIB_A_RangeRetry11.retry, `PV_LIB_A_RangeRetry11.pending_retry, `PV_LIB_A_RangeLegacy11.selected, `PV_LIB_A_RangeLegacy11.begin_projects, `PV_LIB_A_RangeLegacy11.initial_poll, `PV_LIB_A_ChainTrace11.storage_quiet, `PV_LIB_A_ChainTrace11.bind_quiet, `PV_LIB_A_ChainTrace11.trace, `PV_LIB_A_ChainTrace11.corrected_run, `PV_LIB_A_F6Prefix11.shape, `PV_LIB_A_F6Prefix11.sites, `PV_LIB_A_F6Prefix11.literal_bound, `PV_LIB_A_F6Prefix11.steps16, `PV_LIB_A_F6Prefix11.result16, `PV_LIB_A_F6Prefix11.prologue_run, `PV_LIB_A_F6Counter11.call_quiet, `PV_LIB_A_F6Counter11.wait_quiet, `PV_LIB_A_F6Counter11.issue, `PV_LIB_A_F6Counter11.poll, `PV_LIB_A_F6Counter11.history18, `PV_LIB_A_F6Thread11.call_quiet, `PV_LIB_A_F6Thread11.wait_quiet, `PV_LIB_A_F6Thread11.issue, `PV_LIB_A_F6Thread11.poll, `PV_LIB_A_F6Thread11.storage, `PV_LIB_A_F6Thread11.segment3, `PV_LIB_A_F6Panic11.call_quiet, `PV_LIB_A_F6Panic11.wait_quiet, `PV_LIB_A_F6Panic11.issue, `PV_LIB_A_F6Panic11.poll, `PV_LIB_A_F6Panic11.storage, `PV_LIB_A_F6Panic11.segment3, `PV_LIB_A_F6EarlyHistory11.threadStore, `PV_LIB_A_F6EarlyHistory11.panicStore, `PV_LIB_A_F6EarlyHistory11.steps, `PV_LIB_A_F6EarlyHistory11.after, `PV_LIB_A_F6EarlyHistory11.continuation, `PV_LIB_A_F6EarlyHistory11.history, `PV_LIB_StoreActionTable.v2PrefixStep11, `PV_LIB_StoreActionTable.v2PrefixAdvance11, `PV_LIB_StoreActionTable.v2PrefixEntry11, `PV_LIB_StoreActionTable.prefix_step11])
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
