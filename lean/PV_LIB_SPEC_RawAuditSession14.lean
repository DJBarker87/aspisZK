import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_StackSize14, `PV_LIB_SPEC_HookKinds14, `PV_LIB_SPEC_SpawnHooks14, `PV_LIB_SPEC_PrefixNative14, `PV_LIB_SPEC_Values14, `PV_LIB_SPEC_Entry14, `PV_LIB_SPEC_EntryPre14, `PV_LIB_SPEC_PrefixEnvironment14, `PV_LIB_SPEC_NativeChecks14, `PV_LIB_SPEC_VectorKinds14, `PV_LIB_SPEC_PreludeValues14, `PV_LIB_SPEC_Assembly14, `PV_LIB_SPEC_AssemblyEnvironment14, `PV_LIB_SPEC_OriginalStart14, `PV_LIB_SPEC_OriginalHistory14, `PV_LIB_SPEC_RawVec14, `PV_LIB_SPEC_ReachedNative14, `PV_LIB_SPEC_ReachedEnvironment14, `PV_LIB_SPEC_Original14, `PV_LIB_SPEC_ReachedHistory14, `PV_LIB_SPEC_F1Prefix14, `PV_LIB_SPEC_F1Arithmetic14, `PV_LIB_SPEC_F1Force14, `PV_LIB_SPEC_AssembledChecks14, `PV_LIB_SPEC_AssembledSize14, `PV_LIB_SPEC_Worker14, `PV_LIB_SPEC_TlsEntry14, `PV_LIB_SPEC_RawBinding14, `PV_LIB_SPEC_F17Entry14, `PV_LIB_SPEC_TlsOriginal14],
     #[`PV_LIB_SPEC_StackSize14.minimumOffset, `PV_LIB_SPEC_StackSize14.closureKind, `PV_LIB_SPEC_StackSize14.token, `PV_LIB_SPEC_StackSize14.value, `PV_LIB_SPEC_StackSize14.reply, `PV_LIB_SPEC_StackSize14.cached, `PV_LIB_SPEC_StackSize14.other, `PV_LIB_SPEC_HookKinds14.childKind, `PV_LIB_SPEC_HookKinds14.hooksKind, `PV_LIB_SPEC_HookKinds14.vectorKind, `PV_LIB_SPEC_HookKinds14.rawKind, `PV_LIB_SPEC_HookKinds14.innerKind, `PV_LIB_SPEC_HookKinds14.markerKind, `PV_LIB_SPEC_HookKinds14.noneKind, `PV_LIB_SPEC_SpawnHooks14.hooks, `PV_LIB_SPEC_SpawnHooks14.raw, `PV_LIB_SPEC_SpawnHooks14.value, `PV_LIB_SPEC_SpawnHooks14.empty, `PV_LIB_SPEC_SpawnHooks14.thread, `PV_LIB_SPEC_SpawnHooks14.result, `PV_LIB_SPEC_SpawnHooks14.reply, `PV_LIB_SPEC_SpawnHooks14.defaultReply, `PV_LIB_SPEC_SpawnHooks14.fields, `PV_LIB_SPEC_SpawnHooks14.empty_initialized, `PV_LIB_SPEC_SpawnHooks14.output, `PV_LIB_SPEC_SpawnHooks14.other, `PV_LIB_SPEC_PrefixNative14.Cut, `PV_LIB_SPEC_PrefixNative14.core, `PV_LIB_SPEC_PrefixNative14.answer, `PV_LIB_SPEC_PrefixNative14.handler, `PV_LIB_SPEC_PrefixNative14.ordinary_framed, `PV_LIB_SPEC_PrefixNative14.transition, `PV_LIB_SPEC_PrefixNative14.control, `PV_LIB_SPEC_PrefixNative14.step, `PV_LIB_SPEC_PrefixNative14.run, `PV_LIB_SPEC_PrefixNative14.actions, `PV_LIB_SPEC_PrefixNative14.preserves_owner_away, `PV_LIB_SPEC_Values14.width, `PV_LIB_SPEC_Values14.rawNonNull, `PV_LIB_SPEC_Values14.addNonNull, `PV_LIB_SPEC_Values14.subPointer, `PV_LIB_SPEC_Values14.reserve, `PV_LIB_SPEC_Values14.values, `PV_LIB_SPEC_Values14.no_growth, `PV_LIB_SPEC_Values14.growth_gap, `PV_LIB_SPEC_Values14.hooks_empty, `PV_LIB_SPEC_Entry14.hooksSlot, `PV_LIB_SPEC_Entry14.state, `PV_LIB_SPEC_Entry14.input, `PV_LIB_SPEC_Entry14.memory_before, `PV_LIB_SPEC_EntryPre14.memory_before, `PV_LIB_SPEC_EntryPre14.receivers, `PV_LIB_SPEC_EntryPre14.run_bytes, `PV_LIB_SPEC_EntryPre14.n_bytes, `PV_LIB_SPEC_EntryPre14.run_typed, `PV_LIB_SPEC_EntryPre14.n_typed, `PV_LIB_SPEC_EntryPre14.f_typed, `PV_LIB_SPEC_EntryPre14.tasks_typed, `PV_LIB_SPEC_EntryPre14.owner, `PV_LIB_SPEC_EntryPre14.captured, `PV_LIB_SPEC_EntryPre14.pre, `PV_LIB_SPEC_PrefixEnvironment14.native, `PV_LIB_SPEC_PrefixEnvironment14.environment, `PV_LIB_SPEC_PrefixEnvironment14.parameters, `PV_LIB_SPEC_PrefixEnvironment14.pre, `PV_LIB_SPEC_PrefixEnvironment14.allocations, `PV_LIB_SPEC_NativeChecks14.minimum, `PV_LIB_SPEC_NativeChecks14.zero, `PV_LIB_SPEC_NativeChecks14.minimum_bytes, `PV_LIB_SPEC_NativeChecks14.hook_bytes, `PV_LIB_SPEC_NativeChecks14.minimum_word, `PV_LIB_SPEC_NativeChecks14.hook_word, `PV_LIB_SPEC_NativeChecks14.empty_tls, `PV_LIB_SPEC_NativeChecks14.size_value, `PV_LIB_SPEC_NativeChecks14.config, `PV_LIB_SPEC_NativeChecks14.arguments, `PV_LIB_SPEC_NativeChecks14.thread_value, `PV_LIB_SPEC_NativeChecks14.hooks_reply, `PV_LIB_SPEC_VectorKinds14.vectorKind, `PV_LIB_SPEC_VectorKinds14.rawKind, `PV_LIB_SPEC_VectorKinds14.innerKind, `PV_LIB_SPEC_VectorKinds14.markerKind, `PV_LIB_SPEC_PreludeValues14.fn164, `PV_LIB_SPEC_PreludeValues14.fn165, `PV_LIB_SPEC_PreludeValues14.fn93, `PV_LIB_SPEC_PreludeValues14.raw, `PV_LIB_SPEC_PreludeValues14.vector, `PV_LIB_SPEC_PreludeValues14.sizeKind, `PV_LIB_SPEC_PreludeValues14.next, `PV_LIB_SPEC_PreludeValues14.value, `PV_LIB_SPEC_PreludeValues14.reply, `PV_LIB_SPEC_PreludeValues14.rangeKind, `PV_LIB_SPEC_PreludeValues14.config, `PV_LIB_SPEC_PreludeValues14.arguments, `PV_LIB_SPEC_PreludeValues14.range_next, `PV_LIB_SPEC_PreludeValues14.none_tag, `PV_LIB_SPEC_PreludeValues14.some_tag, `PV_LIB_SPEC_PreludeValues14.other, `PV_LIB_SPEC_Assembly14.Cut, `PV_LIB_SPEC_Assembly14.core, `PV_LIB_SPEC_Assembly14.answer, `PV_LIB_SPEC_Assembly14.handler, `PV_LIB_SPEC_Assembly14.ordinary_framed, `PV_LIB_SPEC_Assembly14.transition, `PV_LIB_SPEC_Assembly14.control, `PV_LIB_SPEC_Assembly14.step, `PV_LIB_SPEC_Assembly14.run, `PV_LIB_SPEC_Assembly14.actions, `PV_LIB_SPEC_Assembly14.preserves_owner_away, `PV_LIB_SPEC_AssemblyEnvironment14.native, `PV_LIB_SPEC_AssemblyEnvironment14.environment, `PV_LIB_SPEC_AssemblyEnvironment14.parameters, `PV_LIB_SPEC_AssemblyEnvironment14.pre, `PV_LIB_SPEC_AssemblyEnvironment14.allocations, `PV_LIB_SPEC_OriginalStart14.request, `PV_LIB_SPEC_OriginalHistory14.site, `PV_LIB_SPEC_OriginalHistory14.after, `PV_LIB_SPEC_OriginalHistory14.request, `PV_LIB_SPEC_OriginalHistory14.original, `PV_LIB_SPEC_RawVec14.token, `PV_LIB_SPEC_RawVec14.rawKind, `PV_LIB_SPEC_RawVec14.markerKind, `PV_LIB_SPEC_RawVec14.inner, `PV_LIB_SPEC_RawVec14.value, `PV_LIB_SPEC_RawVec14.reply, `PV_LIB_SPEC_RawVec14.dispatch, `PV_LIB_SPEC_RawVec14.fields, `PV_LIB_SPEC_ReachedNative14.Cut, `PV_LIB_SPEC_ReachedNative14.core, `PV_LIB_SPEC_ReachedNative14.answer, `PV_LIB_SPEC_ReachedNative14.handler, `PV_LIB_SPEC_ReachedNative14.ordinary_framed, `PV_LIB_SPEC_ReachedNative14.transition, `PV_LIB_SPEC_ReachedNative14.control, `PV_LIB_SPEC_ReachedNative14.step, `PV_LIB_SPEC_ReachedNative14.run, `PV_LIB_SPEC_ReachedNative14.actions, `PV_LIB_SPEC_ReachedNative14.preserves_owner_away, `PV_LIB_SPEC_ReachedEnvironment14.native, `PV_LIB_SPEC_ReachedEnvironment14.environment, `PV_LIB_SPEC_ReachedEnvironment14.parameters, `PV_LIB_SPEC_ReachedEnvironment14.pre, `PV_LIB_SPEC_ReachedEnvironment14.allocations, `PV_LIB_SPEC_Original14.site, `PV_LIB_SPEC_Original14.after, `PV_LIB_SPEC_Original14.request, `PV_LIB_SPEC_Original14.original, `PV_LIB_SPEC_Original14.bodyEntry, `PV_LIB_SPEC_Original14.enter, `PV_LIB_SPEC_Original14.run_add, `PV_LIB_SPEC_Original14.original_body, `PV_LIB_SPEC_ReachedHistory14.step, `PV_LIB_SPEC_ReachedHistory14.initial, `PV_LIB_SPEC_ReachedHistory14.run, `PV_LIB_SPEC_ReachedHistory14.original, `PV_LIB_SPEC_F1Prefix14.start, `PV_LIB_SPEC_F1Prefix14.after, `PV_LIB_SPEC_F1Prefix14.prepare, `PV_LIB_SPEC_F1Prefix14.original, `PV_LIB_SPEC_F1Arithmetic14.stage, `PV_LIB_SPEC_F1Arithmetic14.after, `PV_LIB_SPEC_F1Arithmetic14.comparison, `PV_LIB_SPEC_F1Arithmetic14.store, `PV_LIB_SPEC_F1Arithmetic14.parents, `PV_LIB_SPEC_F1Arithmetic14.issued, `PV_LIB_SPEC_F1Arithmetic14.original, `PV_LIB_SPEC_F1Force14.after, `PV_LIB_SPEC_F1Force14.forced, `PV_LIB_SPEC_F1Force14.store, `PV_LIB_SPEC_F1Force14.original, `PV_LIB_SPEC_AssembledChecks14.cut, `PV_LIB_SPEC_AssembledChecks14.different, `PV_LIB_SPEC_AssembledChecks14.f454, `PV_LIB_SPEC_AssembledSize14.arguments, `PV_LIB_SPEC_AssembledSize14.different, `PV_LIB_SPEC_AssembledSize14.f295, `PV_LIB_SPEC_Worker14.site, `PV_LIB_SPEC_Worker14.after, `PV_LIB_SPEC_Worker14.pending, `PV_LIB_SPEC_Worker14.issue, `PV_LIB_SPEC_Worker14.push, `PV_LIB_SPEC_Worker14.enter, `PV_LIB_SPEC_Worker14.store, `PV_LIB_SPEC_Worker14.original, `PV_LIB_SPEC_TlsEntry14.key, `PV_LIB_SPEC_TlsEntry14.site, `PV_LIB_SPEC_TlsEntry14.after, `PV_LIB_SPEC_TlsEntry14.enter, `PV_LIB_SPEC_RawBinding14.inline164, `PV_LIB_SPEC_RawBinding14.at268, `PV_LIB_SPEC_RawBinding14.bound268, `PV_LIB_SPEC_F17Entry14.site, `PV_LIB_SPEC_F17Entry14.after, `PV_LIB_SPEC_F17Entry14.enter, `PV_LIB_SPEC_TlsOriginal14.workerStore, `PV_LIB_SPEC_TlsOriginal14.workerParents, `PV_LIB_SPEC_TlsOriginal14.workerIssued, `PV_LIB_SPEC_TlsOriginal14.original32, `PV_LIB_SPEC_TlsOriginal14.withStore, `PV_LIB_SPEC_TlsOriginal14.withParents, `PV_LIB_SPEC_TlsOriginal14.withIssued, `PV_LIB_SPEC_TlsOriginal14.atTryWith, `PV_LIB_SPEC_TlsOriginal14.original40, `PV_LIB_SPEC_TlsOriginal14.world40, `PV_LIB_SPEC_TlsOriginal14.no_native40])
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
