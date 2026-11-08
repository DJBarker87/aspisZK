import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_NativeChecks14, `PV_LIB_SPEC_NativeConstructors, `PV_LIB_SPEC_NativeContext18, `PV_LIB_SPEC_NativeDelivery16, `PV_LIB_SPEC_NativeHistory, `PV_LIB_SPEC_NativeKinds, `PV_LIB_SPEC_NativeMemory12, `PV_LIB_SPEC_NativeModel, `PV_LIB_SPEC_NativeObligations17, `PV_LIB_SPEC_NativeRecheck12, `PV_LIB_SPEC_NativeRuntime, `PV_LIB_SPEC_NativeTargets18, `PV_LIB_SPEC_Original14, `PV_LIB_SPEC_OriginalHistory14, `PV_LIB_SPEC_OriginalStackGap17, `PV_LIB_SPEC_OriginalStart14, `PV_LIB_SPEC_OwnInitComposition, `PV_LIB_SPEC_OwnInitCut92, `PV_LIB_SPEC_OwnInitCut92Contract, `PV_LIB_SPEC_OwnInitEntry]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_NativeChecks14.config, `PV_LIB_SPEC_NativeChecks14.empty_tls, `PV_LIB_SPEC_NativeChecks14.hook_bytes, `PV_LIB_SPEC_NativeChecks14.hook_word, `PV_LIB_SPEC_NativeChecks14.hooks_reply, `PV_LIB_SPEC_NativeChecks14.minimum, `PV_LIB_SPEC_NativeChecks14.minimum_bytes, `PV_LIB_SPEC_NativeChecks14.minimum_word, `PV_LIB_SPEC_NativeChecks14.size_value, `PV_LIB_SPEC_NativeChecks14.thread_value, `PV_LIB_SPEC_NativeChecks14.zero, `PV_LIB_SPEC_NativeConstructors.atomicBool, `PV_LIB_SPEC_NativeConstructors.boolCell, `PV_LIB_SPEC_NativeConstructors.framed, `PV_LIB_SPEC_NativeConstructors.initial_scope, `PV_LIB_SPEC_NativeConstructors.other, `PV_LIB_SPEC_NativeConstructors.reply, `PV_LIB_SPEC_NativeConstructors.returned, `PV_LIB_SPEC_NativeConstructors.selected, `PV_LIB_SPEC_NativeConstructors.value, `PV_LIB_SPEC_NativeContext18.bound, `PV_LIB_SPEC_NativeContext18.prefix_wait, `PV_LIB_SPEC_NativeContext18.shape, `PV_LIB_SPEC_NativeDelivery16.full, `PV_LIB_SPEC_NativeHistory.initial, `PV_LIB_SPEC_NativeHistory.original, `PV_LIB_SPEC_NativeHistory.run, `PV_LIB_SPEC_NativeHistory.step, `PV_LIB_SPEC_NativeKinds.atomicBool, `PV_LIB_SPEC_NativeKinds.boolCell, `PV_LIB_SPEC_NativeKinds.maybeDangling, `PV_LIB_SPEC_NativeKinds.unsafeCell, `PV_LIB_SPEC_NativeMemory12.Cut, `PV_LIB_SPEC_NativeMemory12.actions, `PV_LIB_SPEC_NativeMemory12.answer, `PV_LIB_SPEC_NativeMemory12.control, `PV_LIB_SPEC_NativeMemory12.core, `PV_LIB_SPEC_NativeMemory12.handler, `PV_LIB_SPEC_NativeMemory12.ordinary_framed, `PV_LIB_SPEC_NativeMemory12.preserves_owner_away, `PV_LIB_SPEC_NativeMemory12.run, `PV_LIB_SPEC_NativeMemory12.step, `PV_LIB_SPEC_NativeMemory12.transition, `PV_LIB_SPEC_NativeModel.actions, `PV_LIB_SPEC_NativeModel.answer, `PV_LIB_SPEC_NativeModel.callback, `PV_LIB_SPEC_NativeModel.control, `PV_LIB_SPEC_NativeModel.handler, `PV_LIB_SPEC_NativeModel.isArc, `PV_LIB_SPEC_NativeModel.ordinary_framed, `PV_LIB_SPEC_NativeModel.preserves_owner_away, `PV_LIB_SPEC_NativeModel.run, `PV_LIB_SPEC_NativeModel.step, `PV_LIB_SPEC_NativeModel.transition, `PV_LIB_SPEC_NativeObligations17.ActiveBeforeF6, `PV_LIB_SPEC_NativeObligations17.AtNative, `PV_LIB_SPEC_NativeObligations17.Hooks, `PV_LIB_SPEC_NativeObligations17.OriginalStack, `PV_LIB_SPEC_NativeObligations17.StackSize, `PV_LIB_SPEC_NativeObligations17.bound, `PV_LIB_SPEC_NativeObligations17.no_original_stack, `PV_LIB_SPEC_NativeRecheck12.boolFn, `PV_LIB_SPEC_NativeRecheck12.bool_value, `PV_LIB_SPEC_NativeRecheck12.capture_constructor]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_NativeRecheck12.cellFn, `PV_LIB_SPEC_NativeRecheck12.cell_value, `PV_LIB_SPEC_NativeRecheck12.danglingFn, `PV_LIB_SPEC_NativeRecheck12.dangling_value, `PV_LIB_SPEC_NativeRecheck12.packet_reply, `PV_LIB_SPEC_NativeRecheck12.scope_handler, `PV_LIB_SPEC_NativeRuntime.ABI, `PV_LIB_SPEC_NativeRuntime.GhostFrame, `PV_LIB_SPEC_NativeRuntime.backend_framed, `PV_LIB_SPEC_NativeRuntime.invalidPure, `PV_LIB_SPEC_NativeRuntime.machineAt, `PV_LIB_SPEC_NativeRuntime.native, `PV_LIB_SPEC_NativeRuntime.pureValue, `PV_LIB_SPEC_NativeRuntime.step, `PV_LIB_SPEC_NativeRuntime.values, `PV_LIB_SPEC_NativeTargets18.ActiveBeforeF6, `PV_LIB_SPEC_NativeTargets18.AtNative, `PV_LIB_SPEC_NativeTargets18.Hooks, `PV_LIB_SPEC_NativeTargets18.OriginalStack, `PV_LIB_SPEC_NativeTargets18.StackAtCallback, `PV_LIB_SPEC_NativeTargets18.StackSize, `PV_LIB_SPEC_NativeTargets18.bound, `PV_LIB_SPEC_NativeTargets18.original_stack, `PV_LIB_SPEC_Original14.after, `PV_LIB_SPEC_Original14.bodyEntry, `PV_LIB_SPEC_Original14.enter, `PV_LIB_SPEC_Original14.original, `PV_LIB_SPEC_Original14.original_body, `PV_LIB_SPEC_Original14.request, `PV_LIB_SPEC_Original14.run_add, `PV_LIB_SPEC_Original14.site, `PV_LIB_SPEC_OriginalHistory14.after, `PV_LIB_SPEC_OriginalHistory14.original, `PV_LIB_SPEC_OriginalHistory14.request, `PV_LIB_SPEC_OriginalHistory14.site, `PV_LIB_SPEC_OriginalStackGap17.NativePair, `PV_LIB_SPEC_OriginalStackGap17.original_pair_impossible, `PV_LIB_SPEC_OriginalStackGap17.original_run_base, `PV_LIB_SPEC_OriginalStackGap17.pairedFrame, `PV_LIB_SPEC_OriginalStackGap17.repaired_excludes_original, `PV_LIB_SPEC_OriginalStackGap17.repaired_pair, `PV_LIB_SPEC_OriginalStart14.request, `PV_LIB_SPEC_OwnInitComposition.AllocationBranch, `PV_LIB_SPEC_OwnInitComposition.AllocationExport, `PV_LIB_SPEC_OwnInitComposition.Contracts, `PV_LIB_SPEC_OwnInitComposition.Implementations, `PV_LIB_SPEC_OwnInitComposition.OwnershipExport, `PV_LIB_SPEC_OwnInitComposition.Witness, `PV_LIB_SPEC_OwnInitCut92.AllocationWitness, `PV_LIB_SPEC_OwnInitCut92.Input, `PV_LIB_SPEC_OwnInitCut92.Representation, `PV_LIB_SPEC_OwnInitCut92.entry, `PV_LIB_SPEC_OwnInitCut92.source_cut, `PV_LIB_SPEC_OwnInitCut92.source_site, `PV_LIB_SPEC_OwnInitCut92Contract.Contract, `PV_LIB_SPEC_OwnInitCut92Contract.Input, `PV_LIB_SPEC_OwnInitCut92Contract.Post, `PV_LIB_SPEC_OwnInitCut92Contract.Representation, `PV_LIB_SPEC_OwnInitCut92Contract.entry, `PV_LIB_SPEC_OwnInitEntry.bytes, `PV_LIB_SPEC_OwnInitEntry.captures]
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
