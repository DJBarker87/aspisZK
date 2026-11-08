import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[ `PV_LIB_A_CellSetBegin, `PV_LIB_A_CellSetMetadata, `PV_LIB_A_CellSetPatch, `PV_LIB_A_ActionPolling, `PV_LIB_A_ThreadCloneStore, `PV_LIB_A_CellSetThreadId, `PV_LIB_A_WeakDropSource, `PV_LIB_A_StoreActionTable7, `PV_LIB_A_WeakDropBranches, `PV_LIB_A_DeferredActions, `PV_LIB_A_SourceReplies7, `PV_LIB_A_Emitted486, `PV_LIB_A_Emitted584, `PV_LIB_A_Emitted608, `PV_LIB_A_Emitted214, `PV_LIB_A_Emitted168, `PV_LIB_A_Emitted122, `PV_LIB_A_Emitted128, `PV_LIB_A_Emitted14, `PV_LIB_A_TypedDropSource, `PV_LIB_A_EmittedDropBinding],
     #[ `PV_LIB_A_CellSetBegin.member, `PV_LIB_A_CellSetBegin.destructor, `PV_LIB_A_CellSetBegin.trivial, `PV_LIB_A_CellSetBegin.PV_THR2_LibrarySemantics_CellSetBegin504, `PV_LIB_A_CellSetBegin.PV_THR2_LibrarySemantics_CellSetTrivial504, `PV_LIB_A_CellSetBegin.begin_from_source, `PV_LIB_A_CellSetBegin.old_retained, `PV_LIB_A_CellSetMetadata.metadata417, `PV_LIB_A_CellSetMetadata.trivial417, `PV_LIB_A_CellSetMetadata.metadata437, `PV_LIB_A_CellSetMetadata.trivial437, `PV_LIB_A_CellSetMetadata.metadata477, `PV_LIB_A_CellSetMetadata.trivial477, `PV_LIB_A_CellSetMetadata.metadata602, `PV_LIB_A_CellSetMetadata.trivial602, `PV_LIB_A_CellSetMetadata.metadata629, `PV_LIB_A_CellSetMetadata.trivial629, `PV_LIB_A_CellSetMetadata.metadata762, `PV_LIB_A_CellSetMetadata.trivial762, `PV_LIB_A_CellSetPatch.select, `PV_LIB_A_CellSetPatch.deliver, `PV_LIB_A_CellSetPatch.step, `PV_LIB_A_CellSetPatch.agreement, `PV_LIB_A_CellSetPatch.full_reply, `PV_LIB_A_ActionPolling.projection, `PV_LIB_A_ActionPolling.receive, `PV_LIB_A_ActionPolling.begin, `PV_LIB_A_ActionPolling.step, `PV_LIB_A_ActionPolling.retry, `PV_LIB_A_ActionPolling.pending, `PV_LIB_A_ActionPolling.pending_retry, `PV_LIB_A_ActionPolling.agreement, `PV_LIB_A_ThreadCloneStore.pointer, `PV_LIB_A_ThreadCloneStore.PV_THR2_LibrarySemantics_ThreadCloneSource214, `PV_LIB_A_ThreadCloneStore.pointer_from_source, `PV_LIB_A_ThreadCloneStore.source_count, `PV_LIB_A_CellSetThreadId.optionThreadId, `PV_LIB_A_CellSetThreadId.effectFree, `PV_LIB_A_CellSetThreadId.PV_THR2_LibrarySemantics_CellSetCopy504, `PV_LIB_A_CellSetThreadId.emitted477, `PV_LIB_A_CellSetThreadId.emitted_copy_cases, `PV_LIB_A_CellSetThreadId.emitted_nontrivial_cases, `PV_LIB_A_CellSetThreadId.copy_from_source, `PV_LIB_A_WeakDropSource.pointer, `PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683, `PV_LIB_A_WeakDropSource.finish, `PV_LIB_A_WeakDropSource.pending, `PV_LIB_A_WeakDropSource.failure, `PV_LIB_A_WeakDropSource.fault, `PV_LIB_A_WeakDropSource.last_deallocate, `PV_LIB_A_WeakDropSource.dangling, `PV_LIB_StoreActionTable.v2Source, `PV_LIB_StoreActionTable.sourceCoverage, `PV_LIB_StoreActionTable.start, `PV_LIB_StoreActionTable.sourceSelect, `PV_LIB_StoreActionTable.sourceReceive, `PV_LIB_StoreActionTable.sourceBegin, `PV_LIB_StoreActionTable.sourceStep, `PV_LIB_StoreActionTable.source_agreement, `PV_LIB_StoreActionTable.source_native, `PV_LIB_StoreActionTable.source_pending, `PV_LIB_StoreActionTable.source_done_reply, `PV_LIB_A_WeakDropBranches.allocated, `PV_LIB_A_WeakDropBranches.last_source, `PV_LIB_A_WeakDropBranches.free_root, `PV_LIB_A_WeakDropBranches.free_other_root, `PV_LIB_A_DeferredActions.action, `PV_LIB_A_DeferredActions.deferred, `PV_LIB_A_DeferredActions.classified, `PV_LIB_A_DeferredActions.pending_start, `PV_LIB_A_DeferredActions.step, `PV_LIB_A_DeferredActions.deferred_retry, `PV_LIB_A_DeferredActions.deferred_pending, `PV_LIB_A_DeferredActions.agreement, `PV_LIB_A_SourceReplies7.copy_all_replies, `PV_LIB_A_SourceReplies7.weak_success, `PV_LIB_A_SourceReplies7.weak_failure, `PV_LIB_A_SourceReplies7.weak_divergence, `PV_LIB_A_SourceReplies7.weak_fault, `PV_LIB_A_SourceReplies7.nontrivial_still_unsupported, `PV_LIB_A_Emitted486.program, `PV_LIB_A_Emitted584.program, `PV_LIB_A_Emitted608.program, `PV_LIB_A_Emitted214.program, `PV_LIB_A_Emitted168.program, `PV_LIB_A_Emitted122.program, `PV_LIB_A_Emitted128.program, `PV_LIB_A_Emitted14.program, `PV_LIB_A_TypedDropSource.callToken, `PV_LIB_A_TypedDropSource.select, `PV_LIB_A_TypedDropSource.enter, `PV_LIB_A_TypedDropSource.step, `PV_LIB_A_TypedDropSource.resolved, `PV_LIB_A_TypedDropSource.agreement, `PV_LIB_A_TypedDropSource.entry_frame, `PV_LIB_A_EmittedDropBinding.programs, `PV_LIB_A_EmittedDropBinding.fnPtr608, `PV_LIB_A_EmittedDropBinding.exact_program, `PV_LIB_A_EmittedDropBinding.selected608])
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
