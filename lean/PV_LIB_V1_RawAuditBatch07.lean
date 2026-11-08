import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_SourceCellFrame14, `PV_LIB_A_SourceContinuation12, `PV_LIB_A_SourceReplies7, `PV_LIB_A_SourceSelectCongruence14, `PV_LIB_A_SourceSequence13, `PV_LIB_A_SourceWriters, `PV_LIB_A_SpawnEnter12, `PV_LIB_A_SpawnHooksTailGap, `PV_LIB_A_StoreAtomicV2, `PV_LIB_A_StoreCounterV2, `PV_LIB_A_StoreDispatchV2, `PV_LIB_A_StorePrimitiveV2, `PV_LIB_A_StrongCount10, `PV_LIB_A_StructuredFrontier13, `PV_LIB_A_StructuredTrace12, `PV_LIB_A_TableCongruence14, `PV_LIB_A_ThreadCloneStore, `PV_LIB_A_ThreadInitBacking9, `PV_LIB_A_TypedBindingFacts, `PV_LIB_A_TypedBody218, `PV_LIB_A_TypedBody222, `PV_LIB_A_TypedBody315, `PV_LIB_A_TypedBody405, `PV_LIB_A_TypedBody486, `PV_LIB_A_TypedBody584, `PV_LIB_A_TypedBody608, `PV_LIB_A_TypedBody661, `PV_LIB_A_TypedDestruct, `PV_LIB_A_TypedDrop178, `PV_LIB_A_TypedDropSource]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_SourceCellFrame14.Below, `PV_LIB_A_SourceCellFrame14.located, `PV_LIB_A_SourceCellFrame14.refl, `PV_LIB_A_SourceCellFrame14.trans, `PV_LIB_A_SourceCellFrame14.writeAddress_frame, `PV_LIB_A_SourceCellFrame14.write_frame, `PV_LIB_A_SourceContinuation12.after, `PV_LIB_A_SourceContinuation12.run, `PV_LIB_A_SourceContinuation12.steps, `PV_LIB_A_SourceReplies7.copy_all_replies, `PV_LIB_A_SourceReplies7.nontrivial_still_unsupported, `PV_LIB_A_SourceReplies7.weak_divergence, `PV_LIB_A_SourceReplies7.weak_failure, `PV_LIB_A_SourceReplies7.weak_fault, `PV_LIB_A_SourceReplies7.weak_success, `PV_LIB_A_SourceSelectCongruence14.select, `PV_LIB_A_SourceSequence13.aggregate_quiet, `PV_LIB_A_SourceSequence13.certified, `PV_LIB_A_SourceSequence13.run, `PV_LIB_A_SourceWriters.installed, `PV_LIB_A_SourceWriters.meanings, `PV_LIB_A_SpawnEnter12.enter270, `PV_LIB_A_SpawnEnter12.enter270Programs, `PV_LIB_A_SpawnEnter12.enter270_trace, `PV_LIB_A_SpawnEnter12.spawn, `PV_LIB_A_SpawnEnter12.spawnPrograms, `PV_LIB_A_SpawnEnter12.spawn_trace, `PV_LIB_A_SpawnHooksTailGap.actual_arc_cleanup, `PV_LIB_A_SpawnHooksTailGap.actual_tail, `PV_LIB_A_SpawnHooksTailGap.no_option_body, `PV_LIB_A_SpawnHooksTailGap.option_source_unbound, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_AtomicBoolStore646, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CellSet504, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchange555, `PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchangeWeak530, `PV_LIB_A_StoreAtomicV2.bool_cast, `PV_LIB_A_StoreAtomicV2.cas_error, `PV_LIB_A_StoreCounterV2.cas_counter, `PV_LIB_A_StoreCounterV2.celltake_counter, `PV_LIB_A_StoreCounterV2.modify_counter, `PV_LIB_A_StoreCounterV2.new_actions_counter, `PV_LIB_A_StoreCounterV2.none_counter, `PV_LIB_A_StoreCounterV2.numbered_after_action, `PV_LIB_A_StoreCounterV2.primitive_counter, `PV_LIB_A_StoreCounterV2.put_counter, `PV_LIB_A_StoreCounterV2.read_bind, `PV_LIB_A_StoreCounterV2.same_counter, `PV_LIB_A_StoreCounterV2.scope_actions_counter, `PV_LIB_A_StoreCounterV2.store_bind, `PV_LIB_A_StoreCounterV2.write_counter, `PV_LIB_A_StoreDispatchV2.agreement_owner, `PV_LIB_A_StoreDispatchV2.agreement_v1, `PV_LIB_A_StoreDispatchV2.effects, `PV_LIB_A_StoreDispatchV2.interpret, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicBoolStore646, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_AtomicStore557, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_FetchAdd351, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_FetchSub581, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_MemReplace442, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_PtrWrite308, `PV_LIB_A_StorePrimitiveV2.PV_THR2_LibrarySemantics_PtrWrite364, `PV_LIB_A_StorePrimitiveV2.load_store_frame, `PV_LIB_A_StorePrimitiveV2.put_root, `PV_LIB_A_StrongCount10.inner]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_StrongCount10.native_table, `PV_LIB_A_StrongCount10.read_count, `PV_LIB_A_StrongCount10.selected, `PV_LIB_A_StrongCount10.site, `PV_LIB_A_StrongCount10.snapshot, `PV_LIB_A_StrongCount10.write_count, `PV_LIB_A_StructuredFrontier13.after, `PV_LIB_A_StructuredFrontier13.cost, `PV_LIB_A_StructuredFrontier13.finish, `PV_LIB_A_StructuredFrontier13.fn, `PV_LIB_A_StructuredFrontier13.node, `PV_LIB_A_StructuredFrontier13.run, `PV_LIB_A_StructuredFrontier13.source, `PV_LIB_A_StructuredFrontier13.steps, `PV_LIB_A_StructuredTrace12.enter_quiet, `PV_LIB_A_StructuredTrace12.issue_quiet, `PV_LIB_A_StructuredTrace12.trace, `PV_LIB_A_TableCongruence14.source, `PV_LIB_A_TableCongruence14.step, `PV_LIB_A_ThreadCloneStore.PV_THR2_LibrarySemantics_ThreadCloneSource214, `PV_LIB_A_ThreadCloneStore.pointer, `PV_LIB_A_ThreadCloneStore.pointer_from_source, `PV_LIB_A_ThreadCloneStore.source_count, `PV_LIB_A_ThreadInitBacking9.registration, `PV_LIB_A_TypedBindingFacts.arcType, `PV_LIB_A_TypedBindingFacts.arc_allocator_unbound, `PV_LIB_A_TypedBindingFacts.empty, `PV_LIB_A_TypedBindingFacts.erased_allocator_not_noop, `PV_LIB_A_TypedBindingFacts.hooksType, `PV_LIB_A_TypedBindingFacts.hooks_method, `PV_LIB_A_TypedBindingFacts.no_selected_arc_glue, `PV_LIB_A_TypedBindingFacts.slow_specialized, `PV_LIB_A_TypedBindingFacts.typed248_hooks, `PV_LIB_A_TypedBindingFacts.untracked, `PV_LIB_A_TypedBody218.instantiate, `PV_LIB_A_TypedBody218.program, `PV_LIB_A_TypedBody222.instantiate, `PV_LIB_A_TypedBody222.program, `PV_LIB_A_TypedBody315.instantiate, `PV_LIB_A_TypedBody315.program, `PV_LIB_A_TypedBody405.instantiate, `PV_LIB_A_TypedBody405.program, `PV_LIB_A_TypedBody486.instantiate, `PV_LIB_A_TypedBody486.program, `PV_LIB_A_TypedBody584.instantiate, `PV_LIB_A_TypedBody584.program, `PV_LIB_A_TypedBody608.instantiate, `PV_LIB_A_TypedBody608.program, `PV_LIB_A_TypedBody661.instantiate, `PV_LIB_A_TypedBody661.program, `PV_LIB_A_TypedDestruct.encode, `PV_LIB_A_TypedDestruct.fnPtr, `PV_LIB_A_TypedDestruct.generics, `PV_LIB_A_TypedDestruct.generics_roundtrip, `PV_LIB_A_TypedDestruct.normalize, `PV_LIB_A_TypedDestruct.preserves_atom, `PV_LIB_A_TypedDestruct.substitute, `PV_LIB_A_TypedDestruct.substitute_type, `PV_LIB_A_TypedDrop178.installed, `PV_LIB_A_TypedDropSource.agreement, `PV_LIB_A_TypedDropSource.callToken]
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
