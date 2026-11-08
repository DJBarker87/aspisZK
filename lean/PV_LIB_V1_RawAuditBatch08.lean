import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_TypedDropSource, `PV_LIB_A_TypedProgramTable8, `PV_LIB_A_TypedProgramTable9, `PV_LIB_A_Unique612, `PV_LIB_A_UniqueBinding, `PV_LIB_A_UnwindMatch, `PV_LIB_A_UnwindMatchCorrectness, `PV_LIB_A_UnwindReplies, `PV_LIB_A_V2ActualBindings14, `PV_LIB_A_V2Callback14, `PV_LIB_A_V2Composition14, `PV_LIB_A_V2F124Entry14, `PV_LIB_A_V2F6To12414, `PV_LIB_A_V2Frontiers14, `PV_LIB_A_V2NativeFrontier14, `PV_LIB_A_V2Neutral14, `PV_LIB_A_V2Post124To15, `PV_LIB_A_V2PrefixBindings14, `PV_LIB_A_V2PrefixTables14, `PV_LIB_A_V2TableCongruence15, `PV_LIB_A_V2TraceTransport14, `PV_LIB_A_ValueDestruct9, `PV_LIB_A_WeakAllocatorFacts9, `PV_LIB_A_WeakCount10, `PV_LIB_A_WeakDropBranches]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_TypedDropSource.enter, `PV_LIB_A_TypedDropSource.entry_frame, `PV_LIB_A_TypedDropSource.resolved, `PV_LIB_A_TypedDropSource.select, `PV_LIB_A_TypedDropSource.step, `PV_LIB_A_TypedProgramTable8.arc_glue, `PV_LIB_A_TypedProgramTable8.away, `PV_LIB_A_TypedProgramTable8.bind, `PV_LIB_A_TypedProgramTable8.exact, `PV_LIB_A_TypedProgramTable8.hooks_drop, `PV_LIB_A_TypedProgramTable8.inner, `PV_LIB_A_TypedProgramTable8.programs, `PV_LIB_A_TypedProgramTable8.run_hooks, `PV_LIB_A_TypedProgramTable8.selected, `PV_LIB_A_TypedProgramTable9.away, `PV_LIB_A_TypedProgramTable9.bind, `PV_LIB_A_TypedProgramTable9.exact, `PV_LIB_A_TypedProgramTable9.inherited, `PV_LIB_A_TypedProgramTable9.option, `PV_LIB_A_TypedProgramTable9.programs, `PV_LIB_A_TypedProgramTable9.selected, `PV_LIB_A_Unique612.installed, `PV_LIB_A_UniqueBinding.callee, `PV_LIB_A_UniqueBinding.installed, `PV_LIB_A_UnwindMatch.arms, `PV_LIB_A_UnwindMatch.carrier, `PV_LIB_A_UnwindMatch.fields, `PV_LIB_A_UnwindMatch.gap, `PV_LIB_A_UnwindMatch.gapOperator, `PV_LIB_A_UnwindMatch.gap_operator, `PV_LIB_A_UnwindMatch.invalidKey, `PV_LIB_A_UnwindMatch.invalid_key, `PV_LIB_A_UnwindMatch.key, `PV_LIB_A_UnwindMatch.operation, `PV_LIB_A_UnwindMatch.otherwise, `PV_LIB_A_UnwindMatch.variantKey, `PV_LIB_A_UnwindMatch.variant_key, `PV_LIB_A_UnwindMatchCorrectness.gap_is_undefined, `PV_LIB_A_UnwindMatchCorrectness.keys, `PV_LIB_A_UnwindMatchCorrectness.selectArm, `PV_LIB_A_UnwindMatchCorrectness.selection, `PV_LIB_A_UnwindMatchCorrectness.source_selector, `PV_LIB_A_UnwindMatchCorrectness.variants, `PV_LIB_A_UnwindReplies.full_reply, `PV_LIB_A_UnwindReplies.locate_place, `PV_LIB_A_UnwindReplies.read_address, `PV_LIB_A_UnwindReplies.read_fields, `PV_LIB_A_UnwindReplies.read_place, `PV_LIB_A_UnwindReplies.replace_fields, `PV_LIB_A_UnwindReplies.store_result, `PV_LIB_A_UnwindReplies.write_address, `PV_LIB_A_V2ActualBindings14.run121, `PV_LIB_A_V2ActualBindings14.run122, `PV_LIB_A_V2ActualBindings14.run123, `PV_LIB_A_V2ActualBindings14.run124, `PV_LIB_A_V2ActualBindings14.run125, `PV_LIB_A_V2ActualBindings14.run134, `PV_LIB_A_V2ActualBindings14.run15, `PV_LIB_A_V2ActualBindings14.run208, `PV_LIB_A_V2ActualBindings14.run219, `PV_LIB_A_V2ActualBindings14.run220, `PV_LIB_A_V2ActualBindings14.run410, `PV_LIB_A_V2Callback14.exact_tail, `PV_LIB_A_V2Callback14.invoke]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_V2Callback14.issue, `PV_LIB_A_V2Callback14.run, `PV_LIB_A_V2Composition14.advance_add, `PV_LIB_A_V2Composition14.chain, `PV_LIB_A_V2Composition14.chained, `PV_LIB_A_V2Composition14.join, `PV_LIB_A_V2Composition14.joined, `PV_LIB_A_V2F124Entry14.numbered, `PV_LIB_A_V2F124Entry14.run, `PV_LIB_A_V2F6To12414.certified, `PV_LIB_A_V2F6To12414.full_tables, `PV_LIB_A_V2F6To12414.history, `PV_LIB_A_V2F6To12414.route, `PV_LIB_A_V2F6To12414.segments, `PV_LIB_A_V2Frontiers14.issue, `PV_LIB_A_V2Frontiers14.run, `PV_LIB_A_V2Frontiers14.sequence, `PV_LIB_A_V2Frontiers14.structured, `PV_LIB_A_V2NativeFrontier14.run, `PV_LIB_A_V2NativeFrontier14.trace, `PV_LIB_A_V2Neutral14.neutral, `PV_LIB_A_V2Neutral14.select_none, `PV_LIB_A_V2Neutral14.successor_step, `PV_LIB_A_V2Neutral14.table_none, `PV_LIB_A_V2Post124To15.certified, `PV_LIB_A_V2Post124To15.history, `PV_LIB_A_V2Post124To15.route, `PV_LIB_A_V2Post124To15.segments, `PV_LIB_A_V2PrefixBindings14.run121, `PV_LIB_A_V2PrefixBindings14.run122, `PV_LIB_A_V2PrefixBindings14.run123, `PV_LIB_A_V2PrefixBindings14.run124, `PV_LIB_A_V2PrefixBindings14.run125, `PV_LIB_A_V2PrefixBindings14.run134, `PV_LIB_A_V2PrefixBindings14.run15, `PV_LIB_A_V2PrefixBindings14.run208, `PV_LIB_A_V2PrefixBindings14.run219, `PV_LIB_A_V2PrefixBindings14.run220, `PV_LIB_A_V2PrefixBindings14.run410, `PV_LIB_A_V2PrefixTables14.Tables, `PV_LIB_A_V2PrefixTables14.installed, `PV_LIB_A_V2TableCongruence15.Trace, `PV_LIB_A_V2TableCongruence15.run, `PV_LIB_A_V2TableCongruence15.select, `PV_LIB_A_V2TableCongruence15.step, `PV_LIB_A_V2TraceTransport14.run, `PV_LIB_A_V2TraceTransport14.step, `PV_LIB_A_V2TraceTransport14.successor, `PV_LIB_A_ValueDestruct9.inherited, `PV_LIB_A_ValueDestruct9.resolve, `PV_LIB_A_ValueDestruct9.token, `PV_LIB_A_ValueDestruct9.untracked_arc, `PV_LIB_A_WeakAllocatorFacts9.borrowed, `PV_LIB_A_WeakAllocatorFacts9.direct, `PV_LIB_A_WeakAllocatorFacts9.guard_from_arc, `PV_LIB_A_WeakCount10.allocated, `PV_LIB_A_WeakCount10.inner, `PV_LIB_A_WeakCount10.read_count, `PV_LIB_A_WeakCount10.write_count, `PV_LIB_A_WeakDropBranches.allocated, `PV_LIB_A_WeakDropBranches.free_other_root]
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
