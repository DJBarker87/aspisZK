import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_FN_SLICE_f11, `PV_FN_SLICE_f12, `PV_FN_SLICE_f15, `PV_FN_SLICE_f23, `PV_FN_SLICE_f31, `PV_FN_SLICE_f35, `PV_FN_SLICE_f47, `PV_FN_SLICE_f48, `PV_FN_SLICE_f59, `PV_FN_THREAD_f124, `PV_FN_THREAD_f126, `PV_FN_THREAD_f164, `PV_FN_THREAD_f216, `PV_FN_THREAD_f218, `PV_FN_THREAD_f222, `PV_FN_THREAD_f315, `PV_FN_THREAD_f443, `PV_FN_THREAD_f458Closed, `PV_FN_THREAD_f537Contract, `PV_LIB_A_ActionAdequacyGap, `PV_LIB_A_ActionAnswers, `PV_LIB_A_ActionPolling, `PV_LIB_A_AllocationBacking9, `PV_LIB_A_AllocatorProvenance, `PV_LIB_A_ArcDropBinding10, `PV_LIB_A_ArcDropCompare10, `PV_LIB_A_ArcMemoryV2, `PV_LIB_A_ArcPollV2, `PV_LIB_A_ArcPollV3, `PV_LIB_A_ArcStoreV2, `PV_LIB_A_AtomicBoolNewV2, `PV_LIB_A_AtomicReadsV2, `PV_LIB_A_BackingFrame9, `PV_LIB_A_CallFrame13, `PV_LIB_A_CallIssue13, `PV_LIB_A_CallNumbers13, `PV_LIB_A_CallbackBindings14, `PV_LIB_A_CallbackTail14, `PV_LIB_A_Caller124, `PV_LIB_Graph, `PV_LIB_LeafObservation, `PV_LIB_Observation, `PV_LIB_View]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_FN_SLICE_f11.contract, `PV_FN_SLICE_f12.contract, `PV_FN_SLICE_f15.contract, `PV_FN_SLICE_f23.contract, `PV_FN_SLICE_f31.contract, `PV_FN_SLICE_f35.contract, `PV_FN_SLICE_f47.contract, `PV_FN_SLICE_f48.contract, `PV_FN_SLICE_f59.contract, `PV_FN_THREAD_f124.contract, `PV_FN_THREAD_f126.contract, `PV_FN_THREAD_f164.contract, `PV_FN_THREAD_f216.contract, `PV_FN_THREAD_f218.contract, `PV_FN_THREAD_f222.contract, `PV_FN_THREAD_f315.contract, `PV_FN_THREAD_f443.contract, `PV_FN_THREAD_f458.contract, `PV_FN_THREAD_f537.contract, `PV_LIB.abort_prefix, `PV_LIB.abort_state_free, `PV_LIB.counter_irrelevant, `PV_LIB.graph_unique, `PV_LIB.leaf_abort_prefix, `PV_LIB.observe_view, `PV_LIB.store_cells, `PV_LIB.world_events, `PV_LIB_A_ActionAdequacyGap.aggregate_delivery_undefined, `PV_LIB_A_ActionAdequacyGap.aggregate_prefix_defined, `PV_LIB_A_ActionAdequacyGap.aggregate_set_unsupported, `PV_LIB_A_ActionAdequacyGap.installed_wrappers_missing, `PV_LIB_A_ActionAdequacyGap.last_drop_unsupported, `PV_LIB_A_ActionAdequacyGap.set_selected, `PV_LIB_A_ActionAnswers.cas_fault, `PV_LIB_A_ActionAnswers.cas_pending, `PV_LIB_A_ActionAnswers.strong_failure, `PV_LIB_A_ActionAnswers.weak_failure, `PV_LIB_A_ActionAnswers.weak_failure_delivery, `PV_LIB_A_ActionPolling.agreement, `PV_LIB_A_ActionPolling.begin, `PV_LIB_A_ActionPolling.pending, `PV_LIB_A_ActionPolling.pending_retry, `PV_LIB_A_ActionPolling.projection, `PV_LIB_A_ActionPolling.receive, `PV_LIB_A_ActionPolling.retry, `PV_LIB_A_ActionPolling.step, `PV_LIB_A_AllocationBacking9.deallocate, `PV_LIB_A_AllocationBacking9.exact_primitive, `PV_LIB_A_AllocationBacking9.free_lifetime, `PV_LIB_A_AllocationBacking9.no_owned_after_free, `PV_LIB_A_AllocationBacking9.place, `PV_LIB_A_AllocationBacking9.select, `PV_LIB_A_AllocationBacking9.selected, `PV_LIB_A_AllocationBacking9.unregistered, `PV_LIB_A_AllocatorProvenance.allocatorType, `PV_LIB_A_AllocatorProvenance.allocator_literal, `PV_LIB_A_AllocatorProvenance.arcAllocator, `PV_LIB_A_AllocatorProvenance.arcGlue, `PV_LIB_A_AllocatorProvenance.arcKind, `PV_LIB_A_AllocatorProvenance.constructed, `PV_LIB_A_AllocatorProvenance.constructor315_moves_A, `PV_LIB_A_AllocatorProvenance.from_inner, `PV_LIB_A_AllocatorProvenance.globalKind, `PV_LIB_A_AllocatorProvenance.globalType]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_AllocatorProvenance.globalValue, `PV_LIB_A_AllocatorProvenance.global_decoded, `PV_LIB_A_AllocatorProvenance.marker_not_default, `PV_LIB_A_AllocatorProvenance.source_allocator, `PV_LIB_A_AllocatorProvenance.source_glue, `PV_LIB_A_ArcDropBinding10.actual_comparison_destination, `PV_LIB_A_ArcDropBinding10.actual_count_destination, `PV_LIB_A_ArcDropBinding10.corrected_old_one, `PV_LIB_A_ArcDropCompare10.call, `PV_LIB_A_ArcDropCompare10.carrier, `PV_LIB_A_ArcDropCompare10.compare, `PV_LIB_A_ArcDropCompare10.delivery, `PV_LIB_A_ArcDropCompare10.function, `PV_LIB_A_ArcDropCompare10.numeric, `PV_LIB_A_ArcDropCompare10.returnedStore, `PV_LIB_A_ArcDropCompare10.source_branch, `PV_LIB_A_ArcDropCompare10.wait, `PV_LIB_A_ArcMemoryV2.actual12950, `PV_LIB_A_ArcMemoryV2.clone_from_cells, `PV_LIB_A_ArcMemoryV2.read_count, `PV_LIB_A_ArcMemoryV2.write_count, `PV_LIB_A_ArcPollV2.actual_poll, `PV_LIB_A_ArcPollV2.selected, `PV_LIB_A_ArcPollV3.actual_poll, `PV_LIB_A_ArcPollV3.selected, `PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360, `PV_LIB_A_ArcStoreV2.clone_count, `PV_LIB_A_ArcStoreV2.inner_from_source, `PV_LIB_A_ArcStoreV2.valid_inner, `PV_LIB_A_AtomicBoolNewV2.PV_THR2_LibrarySemantics_AtomicBoolNew123, `PV_LIB_A_AtomicBoolNewV2.certified, `PV_LIB_A_AtomicBoolNewV2.held_byte, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicBoolLoad129, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicLoad127, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicLoad528, `PV_LIB_A_AtomicReadsV2.at127, `PV_LIB_A_AtomicReadsV2.at129, `PV_LIB_A_AtomicReadsV2.at528, `PV_LIB_A_AtomicReadsV2.reply_exact, `PV_LIB_A_BackingFrame9.free_registry, `PV_LIB_A_BackingFrame9.native, `PV_LIB_A_BackingFrame9.newer_registration, `PV_LIB_A_CallFrame13.arguments_frame, `PV_LIB_A_CallFrame13.entered_iterator, `PV_LIB_A_CallFrame13.issued_frame, `PV_LIB_A_CallFrame13.returned_iterator, `PV_LIB_A_CallIssue13.after, `PV_LIB_A_CallIssue13.finish, `PV_LIB_A_CallIssue13.run, `PV_LIB_A_CallIssue13.steps, `PV_LIB_A_CallNumbers13.arguments_counter, `PV_LIB_A_CallNumbers13.issued_counter, `PV_LIB_A_CallNumbers13.push_bounds, `PV_LIB_A_CallbackBindings14.callback, `PV_LIB_A_CallbackBindings14.pointer, `PV_LIB_A_CallbackBindings14.unary, `PV_LIB_A_CallbackTail14.cells, `PV_LIB_A_CallbackTail14.cost, `PV_LIB_A_CallbackTail14.result, `PV_LIB_A_CallbackTail14.shape, `PV_LIB_A_Caller124.counts]
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
