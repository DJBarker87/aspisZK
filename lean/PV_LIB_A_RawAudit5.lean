import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_ArcMemoryV2, `PV_LIB_A_ArcPollV2, `PV_LIB_A_ArcPollV3, `PV_LIB_A_ArcStoreV2, `PV_LIB_A_AtomicBoolNewV2, `PV_LIB_A_AtomicReadsV2, `PV_LIB_A_CellSourceV2, `PV_LIB_A_CellTakeV2, `PV_LIB_A_CloneCountV2, `PV_LIB_A_CloneIssuedV2, `PV_LIB_A_ClonePrologueV2, `PV_LIB_A_CloneValidityV2, `PV_LIB_A_DropDispatchV2, `PV_LIB_A_DropStoreV2, `PV_LIB_A_F6DeliveryTransportV2, `PV_LIB_A_OwnerStoreV2, `PV_LIB_A_OwnerStoreV3, `PV_LIB_A_PreActionTraceV2, `PV_LIB_A_PreActionTraceV3, `PV_LIB_A_RangeHistoryV2, `PV_LIB_A_RangeTraceV2, `PV_LIB_A_ScopeDispatchV2, `PV_LIB_A_ScopeStoreV2, `PV_LIB_A_StoreAtomicV2, `PV_LIB_A_StoreCounterV2, `PV_LIB_A_StoreDispatchV2, `PV_LIB_A_StorePrimitiveV2, `PV_LIB_A_WriterRegistryV2],
     #[`PV_LIB_A_ArcMemoryV2.write_count, `PV_LIB_A_ArcMemoryV2.read_count, `PV_LIB_A_ArcMemoryV2.clone_from_cells, `PV_LIB_A_ArcMemoryV2.actual12950, `PV_LIB_A_ArcPollV2.selected, `PV_LIB_A_ArcPollV2.actual_poll, `PV_LIB_A_ArcPollV3.selected, `PV_LIB_A_ArcPollV3.actual_poll, `PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360, `PV_LIB_A_ArcStoreV2.inner_from_source, `PV_LIB_A_ArcStoreV2.clone_count, `PV_LIB_A_ArcStoreV2.valid_inner, `PV_LIB_A_AtomicBoolNewV2.PV_THR2_LibrarySemantics_AtomicBoolNew123, `PV_LIB_A_AtomicBoolNewV2.held_byte, `PV_LIB_A_AtomicBoolNewV2.certified, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicLoad127, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicBoolLoad129, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicLoad528, `PV_LIB_A_AtomicReadsV2.reply_exact, `PV_LIB_A_AtomicReadsV2.at127, `PV_LIB_A_AtomicReadsV2.at129, `PV_LIB_A_AtomicReadsV2.at528, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellSetPrefix504, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellBoolSet504, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellTake641, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellNew371, `PV_LIB_A_CellSourceV2.scalar_set, `PV_LIB_A_CellSourceV2.take_root, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641, `PV_LIB_A_CellTakeV2.default_from_source, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_WeakDropSource683, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_ArcDropPrefix486, `PV_LIB_A_CloneCountV2.from124, `PV_LIB_A_CloneIssuedV2.issued_cell, `PV_LIB_A_CloneIssuedV2.issued_read, `PV_LIB_A_CloneIssuedV2.issue_valid, `PV_LIB_A_CloneIssuedV2.from124, `PV_LIB_A_ClonePrologueV2.quiet, `PV_LIB_A_ClonePrologueV2.trace, `PV_LIB_A_ClonePrologueV2.issue, `PV_LIB_A_ClonePrologueV2.run, `PV_LIB_A_CloneValidityV2.caller17, `PV_LIB_A_CloneValidityV2.foreign, `PV_LIB_A_CloneValidityV2.read_foreign, `PV_LIB_A_CloneValidityV2.from124, `PV_LIB_A_DropDispatchV2.agreement, `PV_LIB_A_DropDispatchV2.advance_agreement, `PV_LIB_A_DropDispatchV2.effects, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_ArcDropNonlast486, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_WeakDropNonlast683, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_OptionTake369, `PV_LIB_A_DropStoreV2.none_from_source, `PV_LIB_A_F6DeliveryTransportV2.prefix_identity, `PV_LIB_A_OwnerStoreV2.agreement, `PV_LIB_A_OwnerStoreV2.advance_agreement, `PV_LIB_A_OwnerStoreV2.effects, `PV_LIB_A_OwnerStoreV3.agreement, `PV_LIB_A_OwnerStoreV3.advance_agreement, `PV_LIB_A_OwnerStoreV3.effects, `PV_LIB_A_PreActionTraceV2.step, `PV_LIB_A_PreActionTraceV2.run, `PV_LIB_A_PreActionTraceV2.append, `PV_LIB_A_PreActionTraceV2.nonwaiting, `PV_LIB_A_PreActionTraceV3.step, `PV_LIB_A_PreActionTraceV3.run, `PV_LIB_A_PreActionTraceV3.append, `PV_LIB_A_PreActionTraceV3.nonwaiting, `PV_LIB_A_RangeHistoryV2.returned165, `PV_LIB_A_RangeHistoryV2.local7, `PV_LIB_A_RangeHistoryV2.poll_local7, `PV_LIB_A_RangeHistoryV2.first93_write, `PV_LIB_A_RangeHistoryV2.original_prefix, `PV_LIB_A_RangeTraceV2.after165_returned, `PV_LIB_A_RangeTraceV2.original_poll, `PV_LIB_A_ScopeDispatchV2.interpret, `PV_LIB_A_ScopeDispatchV2.agreement, `PV_LIB_A_ScopeDispatchV2.effects, `PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457, `PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeDecrement611, `PV_LIB_A_ScopeStoreV2.overflow_restores, `PV_LIB_A_ScopeStoreV2.overflow_not_last, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_AtomicBoolStore646, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CellSet504, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchangeWeak530, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchange555, `PV_LIB_A_StoreAtomicV2.bool_cast, `PV_LIB_A_StoreAtomicV2.cas_error, `PV_LIB_A_StoreCounterV2.none_counter, `PV_LIB_A_StoreCounterV2.same_counter, `PV_LIB_A_StoreCounterV2.read_bind, `PV_LIB_A_StoreCounterV2.store_bind, `PV_LIB_A_StoreCounterV2.write_counter, `PV_LIB_A_StoreCounterV2.put_counter, `PV_LIB_A_StoreCounterV2.modify_counter, `PV_LIB_A_StoreCounterV2.primitive_counter, `PV_LIB_A_StoreCounterV2.cas_counter, `PV_LIB_A_StoreCounterV2.new_actions_counter, `PV_LIB_A_StoreCounterV2.scope_actions_counter, `PV_LIB_A_StoreCounterV2.celltake_counter, `PV_LIB_A_StoreCounterV2.numbered_after_action, `PV_LIB_A_StoreDispatchV2.interpret, `PV_LIB_A_StoreDispatchV2.agreement_v1, `PV_LIB_A_StoreDispatchV2.agreement_owner, `PV_LIB_A_StoreDispatchV2.effects, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_FetchAdd351, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_FetchSub581, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicStore557, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicBoolStore646, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_MemReplace442, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_PtrWrite308, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_PtrWrite364, `PV_LIB_A_StorePrimitiveV2.load_store_frame, `PV_LIB_A_StorePrimitiveV2.put_root, `PV_LIB_A_WriterRegistryV2.native, `PV_LIB_A_WriterRegistryV2.primitive, `PV_LIB_A_WriterRegistryV2.scope, `PV_LIB_A_WriterRegistryV2.celltake, `PV_LIB_A_WriterRegistryV2.arc12950])
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
