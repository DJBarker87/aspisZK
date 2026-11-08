import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_Caller124, `PV_LIB_A_CellDestruct504, `PV_LIB_A_CellDestructFacts, `PV_LIB_A_CellSetBegin, `PV_LIB_A_CellSetMetadata, `PV_LIB_A_CellSetPatch, `PV_LIB_A_CellSetThreadId, `PV_LIB_A_CellSourceV2, `PV_LIB_A_CellTakeV2, `PV_LIB_A_ChainTrace11, `PV_LIB_A_CloneCountV2, `PV_LIB_A_CloneIssuedV2, `PV_LIB_A_ClonePrologueV2, `PV_LIB_A_CloneValidityV2, `PV_LIB_A_ClosureAggregate12, `PV_LIB_A_ContextSource16, `PV_LIB_A_Continuation12, `PV_LIB_A_Continue13, `PV_LIB_A_DeferredActions, `PV_LIB_A_DestructMethods, `PV_LIB_A_DestructionNumbering, `PV_LIB_A_DestructorStep10, `PV_LIB_A_DestructorValues10, `PV_LIB_A_DropDispatchV2, `PV_LIB_A_DropInPlace248, `PV_LIB_A_DropMetadata, `PV_LIB_A_DropStoreV2, `PV_LIB_A_Emitted122, `PV_LIB_A_Emitted128, `PV_LIB_A_Emitted14, `PV_LIB_A_Emitted168]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_Caller124.installed, `PV_LIB_A_Caller124.provider_pre, `PV_LIB_A_CellDestruct504.call_suffix, `PV_LIB_A_CellDestruct504.enter, `PV_LIB_A_CellDestruct504.enter_frame, `PV_LIB_A_CellDestruct504.noop_invalidates, `PV_LIB_A_CellDestruct504.select, `PV_LIB_A_CellDestruct504.site, `PV_LIB_A_CellDestruct504.suffix, `PV_LIB_A_CellDestructFacts.away_holder, `PV_LIB_A_CellDestructFacts.emitted602, `PV_LIB_A_CellDestructFacts.saved_old, `PV_LIB_A_CellDestructFacts.selected_from_source, `PV_LIB_A_CellSetBegin.PV_THR2_LibrarySemantics_CellSetBegin504, `PV_LIB_A_CellSetBegin.PV_THR2_LibrarySemantics_CellSetTrivial504, `PV_LIB_A_CellSetBegin.begin_from_source, `PV_LIB_A_CellSetBegin.destructor, `PV_LIB_A_CellSetBegin.member, `PV_LIB_A_CellSetBegin.old_retained, `PV_LIB_A_CellSetBegin.trivial, `PV_LIB_A_CellSetMetadata.metadata417, `PV_LIB_A_CellSetMetadata.metadata437, `PV_LIB_A_CellSetMetadata.metadata477, `PV_LIB_A_CellSetMetadata.metadata602, `PV_LIB_A_CellSetMetadata.metadata629, `PV_LIB_A_CellSetMetadata.metadata762, `PV_LIB_A_CellSetMetadata.trivial417, `PV_LIB_A_CellSetMetadata.trivial437, `PV_LIB_A_CellSetMetadata.trivial477, `PV_LIB_A_CellSetMetadata.trivial602, `PV_LIB_A_CellSetMetadata.trivial629, `PV_LIB_A_CellSetMetadata.trivial762, `PV_LIB_A_CellSetPatch.agreement, `PV_LIB_A_CellSetPatch.deliver, `PV_LIB_A_CellSetPatch.full_reply, `PV_LIB_A_CellSetPatch.select, `PV_LIB_A_CellSetPatch.step, `PV_LIB_A_CellSetThreadId.PV_THR2_LibrarySemantics_CellSetCopy504, `PV_LIB_A_CellSetThreadId.copy_from_source, `PV_LIB_A_CellSetThreadId.effectFree, `PV_LIB_A_CellSetThreadId.emitted477, `PV_LIB_A_CellSetThreadId.emitted_copy_cases, `PV_LIB_A_CellSetThreadId.emitted_nontrivial_cases, `PV_LIB_A_CellSetThreadId.optionThreadId, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellBoolSet504, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellNew371, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellSetPrefix504, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellTake641, `PV_LIB_A_CellSourceV2.scalar_set, `PV_LIB_A_CellSourceV2.take_root, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_ArcDropPrefix486, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_WeakDropSource683, `PV_LIB_A_CellTakeV2.default_from_source, `PV_LIB_A_ChainTrace11.bind_quiet, `PV_LIB_A_ChainTrace11.corrected_run, `PV_LIB_A_ChainTrace11.storage_quiet, `PV_LIB_A_ChainTrace11.trace, `PV_LIB_A_CloneCountV2.from124, `PV_LIB_A_CloneIssuedV2.from124, `PV_LIB_A_CloneIssuedV2.issue_valid, `PV_LIB_A_CloneIssuedV2.issued_cell, `PV_LIB_A_CloneIssuedV2.issued_read, `PV_LIB_A_ClonePrologueV2.issue]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_ClonePrologueV2.quiet, `PV_LIB_A_ClonePrologueV2.run, `PV_LIB_A_ClonePrologueV2.trace, `PV_LIB_A_CloneValidityV2.caller17, `PV_LIB_A_CloneValidityV2.foreign, `PV_LIB_A_CloneValidityV2.from124, `PV_LIB_A_CloneValidityV2.read_foreign, `PV_LIB_A_ClosureAggregate12.run, `PV_LIB_A_ClosureAggregate12.trace, `PV_LIB_A_ContextSource16.aggregate_source, `PV_LIB_A_ContextSource16.bind_source, `PV_LIB_A_ContextSource16.finish, `PV_LIB_A_ContextSource16.quiet, `PV_LIB_A_ContextSource16.source_result, `PV_LIB_A_ContextSource16.storage_source, `PV_LIB_A_ContextSource16.trace, `PV_LIB_A_Continuation12.run, `PV_LIB_A_Continuation12.trace, `PV_LIB_A_Continue13.run, `PV_LIB_A_DeferredActions.action, `PV_LIB_A_DeferredActions.agreement, `PV_LIB_A_DeferredActions.classified, `PV_LIB_A_DeferredActions.deferred, `PV_LIB_A_DeferredActions.deferred_pending, `PV_LIB_A_DeferredActions.deferred_retry, `PV_LIB_A_DeferredActions.pending_start, `PV_LIB_A_DeferredActions.step, `PV_LIB_A_DestructMethods.adtImpl, `PV_LIB_A_DestructMethods.byType, `PV_LIB_A_DestructMethods.concrete, `PV_LIB_A_DestructMethods.concrete_shape, `PV_LIB_A_DestructMethods.implementation, `PV_LIB_A_DestructMethods.resolve, `PV_LIB_A_DestructionNumbering.cell_entry, `PV_LIB_A_DestructionNumbering.drop_entry, `PV_LIB_A_DestructorStep10.ordinary, `PV_LIB_A_DestructorValues10.aggregate, `PV_LIB_A_DestructorValues10.carrier, `PV_LIB_A_DestructorValues10.literal, `PV_LIB_A_DestructorValues10.metadata, `PV_LIB_A_DestructorValues10.original_unit_missing, `PV_LIB_A_DestructorValues10.reference, `PV_LIB_A_DestructorValues10.unitValue, `PV_LIB_A_DropDispatchV2.advance_agreement, `PV_LIB_A_DropDispatchV2.agreement, `PV_LIB_A_DropDispatchV2.effects, `PV_LIB_A_DropInPlace248.PV_THR2_LibrarySemantics_DropInPlace248, `PV_LIB_A_DropInPlace248.forwarded, `PV_LIB_A_DropInPlace248.forwardedWait, `PV_LIB_A_DropInPlace248.frame, `PV_LIB_A_DropInPlace248.resolution, `PV_LIB_A_DropInPlace248.select, `PV_LIB_A_DropMetadata.lookup, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_ArcDropNonlast486, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_OptionTake369, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_WeakDropNonlast683, `PV_LIB_A_DropStoreV2.none_from_source, `PV_LIB_A_Emitted122.program, `PV_LIB_A_Emitted128.program, `PV_LIB_A_Emitted14.program, `PV_LIB_A_Emitted168.program]
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
