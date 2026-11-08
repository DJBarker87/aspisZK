import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_DestructorValues10, `PV_LIB_A_WeakGuardRun10, `PV_LIB_A_WeakOwnerFree10, `PV_LIB_A_WeakGuardSource10, `PV_LIB_A_DestructorStep10, `PV_LIB_A_WeakGuardCorrected10, `PV_LIB_A_WeakGuardPrefix10, `PV_LIB_A_WeakGuardBuild10, `PV_LIB_A_WeakGuardBuildRun10, `PV_LIB_A_WeakFreePoll10, `PV_LIB_A_WeakGuardBuildPrefix10, `PV_LIB_A_Payload24810, `PV_LIB_A_FetchSubReply10, `PV_LIB_A_FetchSubMachine10, `PV_LIB_A_FetchSubRetry10, `PV_LIB_A_FetchSubSource10, `PV_LIB_A_WeakCount10, `PV_LIB_A_FetchSubPrefixes10, `PV_LIB_A_GuardWeakBegin10, `PV_LIB_A_ArcDropCompare10, `PV_LIB_A_StrongCount10, `PV_LIB_A_StoreActionTable10, `PV_LIB_A_ArcDropBinding10],
     #[`PV_LIB_A_DestructorValues10.unitValue, `PV_LIB_A_DestructorValues10.carrier, `PV_LIB_A_DestructorValues10.metadata, `PV_LIB_A_DestructorValues10.literal, `PV_LIB_A_DestructorValues10.reference, `PV_LIB_A_DestructorValues10.aggregate, `PV_LIB_A_DestructorValues10.original_unit_missing, `PV_LIB_A_WeakGuardRun10.carrier, `PV_LIB_A_WeakGuardRun10.entry, `PV_LIB_A_WeakGuardRun10.call, `PV_LIB_A_WeakGuardRun10.issued, `PV_LIB_A_WeakGuardRun10.issued_graph, `PV_LIB_A_WeakOwnerFree10.step, `PV_LIB_A_WeakOwnerFree10.original_poll_gap, `PV_LIB_A_WeakOwnerFree10.source_fields, `PV_LIB_A_WeakOwnerFree10.retry, `PV_LIB_A_WeakGuardSource10.waiting, `PV_LIB_A_WeakGuardSource10.prepared, `PV_LIB_A_WeakGuardSource10.after, `PV_LIB_A_WeakGuardSource10.run, `PV_LIB_A_WeakGuardSource10.older_cell, `PV_LIB_A_WeakGuardSource10.next_activation, `PV_LIB_A_DestructorStep10.ordinary, `PV_LIB_A_WeakGuardCorrected10.stage, `PV_LIB_A_WeakGuardCorrected10.configuration, `PV_LIB_A_WeakGuardCorrected10.raw_step, `PV_LIB_A_WeakGuardCorrected10.corrected_step, `PV_LIB_A_WeakGuardPrefix10.advance, `PV_LIB_A_WeakGuardPrefix10.run, `PV_LIB_A_WeakGuardPrefix10.source_read, `PV_LIB_A_WeakGuardBuild10.kind, `PV_LIB_A_WeakGuardBuild10.guard, `PV_LIB_A_WeakGuardBuild10.entry, `PV_LIB_A_WeakGuardBuild10.stage, `PV_LIB_A_WeakGuardBuild10.configuration, `PV_LIB_A_WeakGuardBuild10.raw_step, `PV_LIB_A_WeakGuardBuildRun10.corrected_step, `PV_LIB_A_WeakGuardBuildRun10.source_root, `PV_LIB_A_WeakGuardBuildRun10.guard_root, `PV_LIB_A_WeakGuardBuildRun10.allocator, `PV_LIB_A_WeakFreePoll10.carrier, `PV_LIB_A_WeakFreePoll10.graph, `PV_LIB_A_WeakFreePoll10.last_step, `PV_LIB_A_WeakGuardBuildPrefix10.run, `PV_LIB_A_Payload24810.source, `PV_LIB_A_Payload24810.hooks_resolution, `PV_LIB_A_Payload24810.hooks_selected, `PV_LIB_A_FetchSubReply10.PV_THR2_LibrarySemantics_FetchSubValue581, `PV_LIB_A_FetchSubReply10.readOld, `PV_LIB_A_FetchSubReply10.selected, `PV_LIB_A_FetchSubReply10.handler, `PV_LIB_A_FetchSubReply10.returned, `PV_LIB_A_FetchSubReply10.pending, `PV_LIB_A_FetchSubReply10.non_success, `PV_LIB_A_FetchSubReply10.effects, `PV_LIB_A_FetchSubReply10.at_request, `PV_LIB_A_FetchSubReply10.away, `PV_LIB_A_FetchSubMachine10.wrap, `PV_LIB_A_FetchSubMachine10.gap, `PV_LIB_A_FetchSubMachine10.poll, `PV_LIB_A_FetchSubMachine10.step, `PV_LIB_A_FetchSubMachine10.agreement, `PV_LIB_A_FetchSubMachine10.retained, `PV_LIB_A_FetchSubRetry10.graph, `PV_LIB_A_FetchSubRetry10.pending, `PV_LIB_A_FetchSubRetry10.begin, `PV_LIB_A_FetchSubSource10.same_write, `PV_LIB_A_FetchSubSource10.read_source, `PV_LIB_A_FetchSubSource10.atomic_root_read, `PV_LIB_A_WeakCount10.inner, `PV_LIB_A_WeakCount10.read_count, `PV_LIB_A_WeakCount10.write_count, `PV_LIB_A_WeakCount10.allocated, `PV_LIB_A_FetchSubPrefixes10.advance, `PV_LIB_A_FetchSubPrefixes10.nonwaiting, `PV_LIB_A_FetchSubPrefixes10.guard_run, `PV_LIB_A_FetchSubPrefixes10.build_run, `PV_LIB_A_GuardWeakBegin10.pointer, `PV_LIB_A_GuardWeakBegin10.begin, `PV_LIB_A_ArcDropCompare10.numeric, `PV_LIB_A_ArcDropCompare10.carrier, `PV_LIB_A_ArcDropCompare10.call, `PV_LIB_A_ArcDropCompare10.wait, `PV_LIB_A_ArcDropCompare10.returnedStore, `PV_LIB_A_ArcDropCompare10.function, `PV_LIB_A_ArcDropCompare10.delivery, `PV_LIB_A_ArcDropCompare10.compare, `PV_LIB_A_ArcDropCompare10.source_branch, `PV_LIB_A_StrongCount10.inner, `PV_LIB_A_StrongCount10.site, `PV_LIB_A_StrongCount10.read_count, `PV_LIB_A_StrongCount10.write_count, `PV_LIB_A_StrongCount10.snapshot, `PV_LIB_A_StrongCount10.native_table, `PV_LIB_A_StrongCount10.selected, `PV_LIB_StoreActionTable.v2DestructionPrograms10, `PV_LIB_StoreActionTable.v2DestructionStep10, `PV_LIB_StoreActionTable.v2DestructionEntry10, `PV_LIB_StoreActionTable.originalDestructionCarrier10, `PV_LIB_StoreActionTable.destruction_agreement10, `PV_LIB_A_ArcDropBinding10.actual_count_destination, `PV_LIB_A_ArcDropBinding10.actual_comparison_destination, `PV_LIB_A_ArcDropBinding10.corrected_old_one])
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
