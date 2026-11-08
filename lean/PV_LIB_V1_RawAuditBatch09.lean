import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_WeakDropBranches, `PV_LIB_A_WeakDropSource, `PV_LIB_A_WeakFreeAgreement9, `PV_LIB_A_WeakFreeFacts9, `PV_LIB_A_WeakFreePoll10, `PV_LIB_A_WeakGuardBuild10, `PV_LIB_A_WeakGuardBuildPrefix10, `PV_LIB_A_WeakGuardBuildRun10, `PV_LIB_A_WeakGuardCaller9, `PV_LIB_A_WeakGuardCorrected10, `PV_LIB_A_WeakGuardPrefix10, `PV_LIB_A_WeakGuardRun10, `PV_LIB_A_WeakGuardSource10, `PV_LIB_A_WeakOwnerFree10, `PV_LIB_A_WeakOwnerFree9, `PV_LIB_A_WriterNative, `PV_LIB_A_WriterNumbering, `PV_LIB_A_WriterOrdinary, `PV_LIB_A_WriterRegistry, `PV_LIB_A_WriterRegistryV2, `PV_LIB_A_WriterSites, `PV_LIB_Arc124, `PV_LIB_Arc124Allocated, `PV_LIB_Arc124Counts, `PV_LIB_Arc126, `PV_LIB_Arc216, `PV_LIB_Arc222, `PV_LIB_ArcClone360, `PV_LIB_Array11View, `PV_LIB_Array12View, `PV_LIB_Array15View, `PV_LIB_Array23View, `PV_LIB_ArrayInstances, `PV_LIB_Atomic121]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_WeakDropBranches.free_root, `PV_LIB_A_WeakDropBranches.last_source, `PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683, `PV_LIB_A_WeakDropSource.dangling, `PV_LIB_A_WeakDropSource.failure, `PV_LIB_A_WeakDropSource.fault, `PV_LIB_A_WeakDropSource.finish, `PV_LIB_A_WeakDropSource.last_deallocate, `PV_LIB_A_WeakDropSource.pending, `PV_LIB_A_WeakDropSource.pointer, `PV_LIB_A_WeakFreeAgreement9.Neutral, `PV_LIB_A_WeakFreeAgreement9.agreement, `PV_LIB_A_WeakFreeFacts9.erased_allocator, `PV_LIB_A_WeakFreeFacts9.non_success_source, `PV_LIB_A_WeakFreeFacts9.pending, `PV_LIB_A_WeakFreeFacts9.poll_graph, `PV_LIB_A_WeakFreeFacts9.success, `PV_LIB_A_WeakFreePoll10.carrier, `PV_LIB_A_WeakFreePoll10.graph, `PV_LIB_A_WeakFreePoll10.last_step, `PV_LIB_A_WeakGuardBuild10.configuration, `PV_LIB_A_WeakGuardBuild10.entry, `PV_LIB_A_WeakGuardBuild10.guard, `PV_LIB_A_WeakGuardBuild10.kind, `PV_LIB_A_WeakGuardBuild10.raw_step, `PV_LIB_A_WeakGuardBuild10.stage, `PV_LIB_A_WeakGuardBuildPrefix10.run, `PV_LIB_A_WeakGuardBuildRun10.allocator, `PV_LIB_A_WeakGuardBuildRun10.corrected_step, `PV_LIB_A_WeakGuardBuildRun10.guard_root, `PV_LIB_A_WeakGuardBuildRun10.source_root, `PV_LIB_A_WeakGuardCaller9.allocator, `PV_LIB_A_WeakGuardCorrected10.configuration, `PV_LIB_A_WeakGuardCorrected10.corrected_step, `PV_LIB_A_WeakGuardCorrected10.raw_step, `PV_LIB_A_WeakGuardCorrected10.stage, `PV_LIB_A_WeakGuardPrefix10.advance, `PV_LIB_A_WeakGuardPrefix10.run, `PV_LIB_A_WeakGuardPrefix10.source_read, `PV_LIB_A_WeakGuardRun10.call, `PV_LIB_A_WeakGuardRun10.carrier, `PV_LIB_A_WeakGuardRun10.entry, `PV_LIB_A_WeakGuardRun10.issued, `PV_LIB_A_WeakGuardRun10.issued_graph, `PV_LIB_A_WeakGuardSource10.after, `PV_LIB_A_WeakGuardSource10.next_activation, `PV_LIB_A_WeakGuardSource10.older_cell, `PV_LIB_A_WeakGuardSource10.prepared, `PV_LIB_A_WeakGuardSource10.run, `PV_LIB_A_WeakGuardSource10.waiting, `PV_LIB_A_WeakOwnerFree10.original_poll_gap, `PV_LIB_A_WeakOwnerFree10.retry, `PV_LIB_A_WeakOwnerFree10.source_fields, `PV_LIB_A_WeakOwnerFree10.step, `PV_LIB_A_WeakOwnerFree9.allocator, `PV_LIB_A_WeakOwnerFree9.gap, `PV_LIB_A_WeakOwnerFree9.globalType, `PV_LIB_A_WeakOwnerFree9.pending_reply, `PV_LIB_A_WeakOwnerFree9.poll, `PV_LIB_A_WeakOwnerFree9.reply, `PV_LIB_A_WeakOwnerFree9.reply_effects, `PV_LIB_A_WeakOwnerFree9.retry, `PV_LIB_A_WeakOwnerFree9.step, `PV_LIB_A_WeakOwnerFree9.weakAllocator]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_WriterNative.certified10, `PV_LIB_A_WriterNative.certified167, `PV_LIB_A_WriterNative.certified9, `PV_LIB_A_WriterNative.certified93, `PV_LIB_A_WriterNumbering.local_store, `PV_LIB_A_WriterNumbering.write_counter, `PV_LIB_A_WriterOrdinary.installed, `PV_LIB_A_WriterOrdinary.noncatch, `PV_LIB_A_WriterRegistry.installed, `PV_LIB_A_WriterRegistryV2.arc12950, `PV_LIB_A_WriterRegistryV2.celltake, `PV_LIB_A_WriterRegistryV2.native, `PV_LIB_A_WriterRegistryV2.primitive, `PV_LIB_A_WriterRegistryV2.scope, `PV_LIB_A_WriterSites.installed, `PV_LIB_A_WriterSites.selected, `PV_LIB_A_WriterSites.source3447, `PV_LIB_A_WriterSites.source3519, `PV_LIB_A_WriterSites.source3641, `PV_LIB_A_WriterSites.source3756, `PV_LIB_A_WriterSites.source4327, `PV_LIB_A_WriterSites.source487, `PV_LIB_A_WriterSites.source8248, `PV_LIB_A_WriterSites.source930, `PV_LIB_Arc124.installed, `PV_LIB_Arc124.internal_reached, `PV_LIB_Arc124.law, `PV_LIB_Arc124.model, `PV_LIB_Arc124Allocated.reached, `PV_LIB_Arc124Counts.certified, `PV_LIB_Arc126.internal_reached, `PV_LIB_Arc126.realizes, `PV_LIB_Arc216.installed, `PV_LIB_Arc216.internal_reached, `PV_LIB_Arc216.law, `PV_LIB_Arc216.model, `PV_LIB_Arc222.internal_reached, `PV_LIB_Arc222.realizes, `PV_LIB_ArcClone360.certified, `PV_LIB_ArcClone360.law, `PV_LIB_ArcClone360.model, `PV_LIB_Array11View.abort_prefix, `PV_LIB_Array11View.model, `PV_LIB_Array12View.cells, `PV_LIB_Array12View.installed, `PV_LIB_Array15View.cells, `PV_LIB_Array15View.installed, `PV_LIB_Array23View.cells, `PV_LIB_Array23View.installed, `PV_LIB_ArrayInstances.installed12, `PV_LIB_ArrayInstances.installed15, `PV_LIB_ArrayInstances.installed23, `PV_LIB_ArrayInstances.law12, `PV_LIB_ArrayInstances.law15, `PV_LIB_ArrayInstances.law23, `PV_LIB_ArrayInstances.model12, `PV_LIB_ArrayInstances.model15, `PV_LIB_ArrayInstances.model23, `PV_LIB_Atomic121.certified, `PV_LIB_Atomic121.law, `PV_LIB_Atomic121.model]
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
