import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_LaneA_Graph, `PV_LIB_SPEC_LaneA_View, `PV_LIB_SPEC_LaneA_Observation, `PV_LIB_SPEC_LaneA_A_SourceWriters, `PV_LIB_SPEC_LaneA_A_OwnerStore, `PV_LIB_SPEC_LaneA_A_StorePrimitiveV2, `PV_LIB_SPEC_LaneA_A_ArcStoreV2, `PV_LIB_SPEC_LaneA_A_StoreAtomicV2, `PV_LIB_SPEC_LaneA_A_StoreDispatchV2, `PV_LIB_SPEC_LaneA_A_ScopeStoreV2, `PV_LIB_SPEC_LaneA_A_ScopeDispatchV2, `PV_LIB_SPEC_LaneA_A_CellTakeV2, `PV_LIB_SPEC_LaneA_A_OwnerStoreV2, `PV_LIB_SPEC_LaneA_A_AtomicReadsV2, `PV_LIB_SPEC_LaneA_A_CellSourceV2, `PV_LIB_SPEC_LaneA_A_OwnerStoreV3, `PV_LIB_SPEC_LaneA_A_DropStoreV2, `PV_LIB_SPEC_LaneA_A_DropDispatchV2, `PV_LIB_SPEC_LaneA_A_StoreActionTable, `PV_LIB_SPEC_LaneA_A_StoreActionMachine, `PV_LIB_SPEC_OwnInitCut92, `PV_LIB_SPEC_OwnInitCut92Contract, `PV_LIB_SPEC_Cut92Composition, `PV_LIB_SPEC_V2Runtime, `PV_LIB_SPEC_ScopeAllocationGap, `PV_LIB_SPEC_ScopeAllocationPollGap, `PV_LIB_SPEC_ScopeRuntimeGap],
     #[`PV_LIB.graph_unique, `PV_LIB.abort_state_free, `PV_LIB.store_cells, `PV_LIB.counter_irrelevant, `PV_LIB.world_events, `PV_LIB.abort_prefix, `PV_LIB.observe_view, `PV_LIB_A_SourceWriters.installed, `PV_LIB_A_SourceWriters.meanings, `PV_LIB_A_OwnerStore.agreement, `PV_LIB_A_OwnerStore.installed, `PV_LIB_A_OwnerStore.effects, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_FetchAdd351, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_FetchSub581, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicStore557, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicBoolStore646, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_MemReplace442, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_PtrWrite308, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_PtrWrite364, `PV_LIB_A_StorePrimitiveV2.load_store_frame, `PV_LIB_A_StorePrimitiveV2.put_root, `PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360, `PV_LIB_A_ArcStoreV2.inner_from_source, `PV_LIB_A_ArcStoreV2.clone_count, `PV_LIB_A_ArcStoreV2.valid_inner, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_AtomicBoolStore646, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CellSet504, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchangeWeak530, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchange555, `PV_LIB_A_StoreAtomicV2.bool_cast, `PV_LIB_A_StoreAtomicV2.cas_error, `PV_LIB_A_StoreDispatchV2.interpret, `PV_LIB_A_StoreDispatchV2.agreement_v1, `PV_LIB_A_StoreDispatchV2.agreement_owner, `PV_LIB_A_StoreDispatchV2.effects, `PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457, `PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeDecrement611, `PV_LIB_A_ScopeStoreV2.overflow_restores, `PV_LIB_A_ScopeStoreV2.overflow_not_last, `PV_LIB_A_ScopeDispatchV2.interpret, `PV_LIB_A_ScopeDispatchV2.agreement, `PV_LIB_A_ScopeDispatchV2.effects, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641, `PV_LIB_A_CellTakeV2.default_from_source, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_WeakDropSource683, `PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_ArcDropPrefix486, `PV_LIB_A_OwnerStoreV2.agreement, `PV_LIB_A_OwnerStoreV2.advance_agreement, `PV_LIB_A_OwnerStoreV2.effects, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicLoad127, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicBoolLoad129, `PV_LIB_A_AtomicReadsV2.PV_THR2_LibrarySemantics_AtomicLoad528, `PV_LIB_A_AtomicReadsV2.reply_exact, `PV_LIB_A_AtomicReadsV2.at127, `PV_LIB_A_AtomicReadsV2.at129, `PV_LIB_A_AtomicReadsV2.at528, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellSetPrefix504, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellBoolSet504, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellTake641, `PV_LIB_A_CellSourceV2.PV_THR2_LibrarySemantics_CellNew371, `PV_LIB_A_CellSourceV2.scalar_set, `PV_LIB_A_CellSourceV2.take_root, `PV_LIB_A_OwnerStoreV3.agreement, `PV_LIB_A_OwnerStoreV3.advance_agreement, `PV_LIB_A_OwnerStoreV3.effects, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_ArcDropNonlast486, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_WeakDropNonlast683, `PV_LIB_A_DropStoreV2.PV_THR2_LibrarySemantics_OptionTake369, `PV_LIB_A_DropStoreV2.none_from_source, `PV_LIB_A_DropDispatchV2.agreement, `PV_LIB_A_DropDispatchV2.advance_agreement, `PV_LIB_A_DropDispatchV2.effects, `PV_LIB_StoreActionTable.v2, `PV_LIB_StoreActionTable.coverage, `PV_LIB_StoreActionTable.interpret, `PV_LIB_StoreActionTable.weak_cas, `PV_LIB_StoreActionTable.strong_cas, `PV_LIB_StoreActionTable.clone_all_answers, `PV_LIB_StoreActionTable.scope_overflow, `PV_LIB_StoreActionTable.select, `PV_LIB_StoreActionTable.deliver, `PV_LIB_StoreActionTable.step, `PV_LIB_StoreActionTable.agreement, `PV_LIB_StoreActionTable.native, `PV_LIB_StoreActionTable.effects, `PV_LIB_StoreActionTable.advance_agreement, `PV_LIB_SPEC_OwnInitCut92.Input, `PV_LIB_SPEC_OwnInitCut92.Representation, `PV_LIB_SPEC_OwnInitCut92.entry, `PV_LIB_SPEC_OwnInitCut92.AllocationWitness, `PV_LIB_SPEC_OwnInitCut92.source_cut, `PV_LIB_SPEC_OwnInitCut92.source_site, `PV_LIB_SPEC_OwnInitCut92Contract.Input, `PV_LIB_SPEC_OwnInitCut92Contract.Representation, `PV_LIB_SPEC_OwnInitCut92Contract.entry, `PV_LIB_SPEC_OwnInitCut92Contract.Post, `PV_LIB_SPEC_OwnInitCut92Contract.Contract, `PV_LIB_SPEC_Cut92Composition.Implementations, `PV_LIB_SPEC_Cut92Composition.OwnContract, `PV_LIB_SPEC_Cut92Composition.Contracts, `PV_LIB_SPEC_Cut92Composition.AllocationBranch, `PV_LIB_SPEC_Cut92Composition.Witness, `PV_LIB_SPEC_V2Runtime.transition, `PV_LIB_SPEC_V2Runtime.control, `PV_LIB_SPEC_V2Runtime.step, `PV_LIB_SPEC_V2Runtime.run, `PV_LIB_SPEC_V2Runtime.actions, `PV_LIB_SPEC_V2Runtime.preserves_owner_away, `PV_LIB_SPEC_ScopeAllocationGap.C, `PV_LIB_SPEC_ScopeAllocationGap.K, `PV_LIB_SPEC_ScopeAllocationGap.scope_body, `PV_LIB_SPEC_ScopeAllocationGap.atomic, `PV_LIB_SPEC_ScopeAllocationGap.not_an_option, `PV_LIB_SPEC_ScopeAllocationGap.scope_decode, `PV_LIB_SPEC_ScopeAllocationGap.wrong_layout, `PV_LIB_SPEC_ScopeAllocationPollGap.request, `PV_LIB_SPEC_ScopeAllocationPollGap.rejects, `PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources, `PV_LIB_SPEC_ScopeAllocationPollGap.correct40, `PV_LIB_SPEC_ScopeAllocationPollGap.unbound48, `PV_LIB_SPEC_ScopeRuntimeGap.parameters, `PV_LIB_SPEC_ScopeRuntimeGap.native_none, `PV_LIB_SPEC_ScopeRuntimeGap.answer_none])
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
