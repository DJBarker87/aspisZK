import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_PurePoll, `PV_LIB_A_PureValues, `PV_LIB_A_Range165, `PV_LIB_A_RangeCaptures12, `PV_LIB_A_RangeFirst11, `PV_LIB_A_RangeHistory11, `PV_LIB_A_RangeHistory12, `PV_LIB_A_RangeHistoryV2, `PV_LIB_A_RangeInvariant12, `PV_LIB_A_RangeIteration13, `PV_LIB_A_RangeLegacy11, `PV_LIB_A_RangeMatch12, `PV_LIB_A_RangePoll11, `PV_LIB_A_RangeQuiet11, `PV_LIB_A_RangeReply12, `PV_LIB_A_RangeRetry11, `PV_LIB_A_RangeStartTrace11, `PV_LIB_A_RangeTailTrace11, `PV_LIB_A_RangeTo270History12, `PV_LIB_A_RangeTraceV2, `PV_LIB_A_RangeWriter, `PV_LIB_A_ReplyAdequacyGap, `PV_LIB_A_Residual280, `PV_LIB_A_Return16, `PV_LIB_A_ScopeDispatchV2, `PV_LIB_A_ScopeIncrementShape14, `PV_LIB_A_ScopePayloadIdentityGap14, `PV_LIB_A_ScopePayloadShape14, `PV_LIB_A_ScopeStoreV2, `PV_LIB_A_SequenceFrame14, `PV_LIB_A_SequenceFrontier13]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_PurePoll.installed277, `PV_LIB_A_PurePoll.installed278, `PV_LIB_A_PurePoll.installed279, `PV_LIB_A_PurePoll.installed280, `PV_LIB_A_PurePoll.noncatch, `PV_LIB_A_PurePoll.unlisted_poll, `PV_LIB_A_PureValues.source_local278, `PV_LIB_A_PureValues.source_local279, `PV_LIB_A_Range165.certified, `PV_LIB_A_Range165.law, `PV_LIB_A_Range165.model, `PV_LIB_A_Range165.old_contract_allows_null, `PV_LIB_A_Range165.old_contract_allows_range, `PV_LIB_A_Range165.reply_exact, `PV_LIB_A_Range165.sourceRange_distinct, `PV_LIB_A_Range165.sourceRange_not_null, `PV_LIB_A_RangeCaptures12.break_quiet, `PV_LIB_A_RangeCaptures12.run, `PV_LIB_A_RangeCaptures12.sites, `PV_LIB_A_RangeCaptures12.trace, `PV_LIB_A_RangeFirst11.cell, `PV_LIB_A_RangeFirst11.history, `PV_LIB_A_RangeFirst11.written, `PV_LIB_A_RangeHistory11.corrected_prefix, `PV_LIB_A_RangeHistory11.poll, `PV_LIB_A_RangeHistory11.prefix_trace, `PV_LIB_A_RangeHistory12.history, `PV_LIB_A_RangeHistory12.iterator, `PV_LIB_A_RangeHistoryV2.first93_write, `PV_LIB_A_RangeHistoryV2.local7, `PV_LIB_A_RangeHistoryV2.original_prefix, `PV_LIB_A_RangeHistoryV2.poll_local7, `PV_LIB_A_RangeHistoryV2.returned165, `PV_LIB_A_RangeInvariant12.Iterator, `PV_LIB_A_RangeInvariant12.delivered, `PV_LIB_A_RangeInvariant12.next, `PV_LIB_A_RangeInvariant12.poll, `PV_LIB_A_RangeInvariant12.post, `PV_LIB_A_RangeInvariant12.post_iterator, `PV_LIB_A_RangeInvariant12.prepared, `PV_LIB_A_RangeIteration13.history, `PV_LIB_A_RangeIteration13.prepared, `PV_LIB_A_RangeLegacy11.begin_projects, `PV_LIB_A_RangeLegacy11.initial_poll, `PV_LIB_A_RangeLegacy11.selected, `PV_LIB_A_RangeMatch12.quiet6, `PV_LIB_A_RangeMatch12.quiet7, `PV_LIB_A_RangeMatch12.run, `PV_LIB_A_RangeMatch12.trace, `PV_LIB_A_RangePoll11.poll, `PV_LIB_A_RangePoll11.selected, `PV_LIB_A_RangeQuiet11.loop0, `PV_LIB_A_RangeQuiet11.loop1, `PV_LIB_A_RangeQuiet11.loop2, `PV_LIB_A_RangeQuiet11.loop3, `PV_LIB_A_RangeQuiet11.loop4, `PV_LIB_A_RangeQuiet11.loop5, `PV_LIB_A_RangeQuiet11.main10, `PV_LIB_A_RangeQuiet11.main11, `PV_LIB_A_RangeQuiet11.main12, `PV_LIB_A_RangeQuiet11.main5, `PV_LIB_A_RangeQuiet11.main6, `PV_LIB_A_RangeQuiet11.main7, `PV_LIB_A_RangeQuiet11.main8]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_RangeQuiet11.main9, `PV_LIB_A_RangeReply12.after, `PV_LIB_A_RangeReply12.deliveredStore, `PV_LIB_A_RangeReply12.iterator, `PV_LIB_A_RangeReply12.returned, `PV_LIB_A_RangeReply12.returnedStore, `PV_LIB_A_RangeReply12.run, `PV_LIB_A_RangeReply12.steps, `PV_LIB_A_RangeRetry11.pending, `PV_LIB_A_RangeRetry11.pending_retry, `PV_LIB_A_RangeRetry11.retry, `PV_LIB_A_RangeStartTrace11.call2, `PV_LIB_A_RangeStartTrace11.cons_run, `PV_LIB_A_RangeStartTrace11.prefix5, `PV_LIB_A_RangeStartTrace11.storage2, `PV_LIB_A_RangeStartTrace11.wait165, `PV_LIB_A_RangeTailTrace11.enter7, `PV_LIB_A_RangeTailTrace11.loop6, `PV_LIB_A_RangeTailTrace11.move3, `PV_LIB_A_RangeTo270History12.history, `PV_LIB_A_RangeTraceV2.after165_returned, `PV_LIB_A_RangeTraceV2.original_poll, `PV_LIB_A_RangeWriter.range93, `PV_LIB_A_ReplyAdequacyGap.panic_not_retained, `PV_LIB_A_ReplyAdequacyGap.panic_reply, `PV_LIB_A_ReplyAdequacyGap.pending_not_retained, `PV_LIB_A_ReplyAdequacyGap.pending_reply, `PV_LIB_A_Residual280.certified, `PV_LIB_A_Residual280.constructors_distinct, `PV_LIB_A_Residual280.old_contract_allows_ok, `PV_LIB_A_Residual280.source_local, `PV_LIB_A_Return16.parent, `PV_LIB_A_Return16.run, `PV_LIB_A_Return16.source, `PV_LIB_A_ScopeDispatchV2.agreement, `PV_LIB_A_ScopeDispatchV2.effects, `PV_LIB_A_ScopeDispatchV2.interpret, `PV_LIB_A_ScopeIncrementShape14.increment, `PV_LIB_A_ScopeIncrementShape14.zero_increment, `PV_LIB_A_ScopePayloadIdentityGap14.checked, `PV_LIB_A_ScopePayloadIdentityGap14.initial, `PV_LIB_A_ScopePayloadIdentityGap14.not_fixed_payload, `PV_LIB_A_ScopePayloadShape14.overwrite, `PV_LIB_A_ScopePayloadShape14.read_count, `PV_LIB_A_ScopePayloadShape14.reference, `PV_LIB_A_ScopePayloadShape14.replace_count, `PV_LIB_A_ScopePayloadShape14.write_count, `PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeDecrement611, `PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457, `PV_LIB_A_ScopeStoreV2.overflow_not_last, `PV_LIB_A_ScopeStoreV2.overflow_restores, `PV_LIB_A_SequenceFrame14.Safe, `PV_LIB_A_SequenceFrame14.bound_frame, `PV_LIB_A_SequenceFrame14.result_frame, `PV_LIB_A_SequenceFrame14.storeOf, `PV_LIB_A_SequenceFrontier13.after, `PV_LIB_A_SequenceFrontier13.cost, `PV_LIB_A_SequenceFrontier13.finish, `PV_LIB_A_SequenceFrontier13.prepend, `PV_LIB_A_SequenceFrontier13.run, `PV_LIB_A_SequenceFrontier13.steps]
@[noinline] private def v1Roots : Array Name := v1Roots0 ++ v1Roots1
-- V1_ARRAYS_END
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (v1Modules, v1Roots)
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
