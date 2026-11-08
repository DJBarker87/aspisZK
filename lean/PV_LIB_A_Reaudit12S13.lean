import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_RangeMatch12, `PV_LIB_A_RangeCaptures12, `PV_LIB_A_RangeReply12, `PV_LIB_A_RangeHistory12, `PV_LIB_A_Continuation12, `PV_LIB_A_ClosureAggregate12, `PV_LIB_A_StructuredTrace12, `PV_LIB_A_F166Chains12, `PV_LIB_A_SpawnEnter12, `PV_LIB_A_F166Builder12, `PV_LIB_A_RangeInvariant12, `PV_LIB_A_F166History12, `PV_LIB_A_SourceContinuation12, `PV_LIB_A_Post93Prefix12, `PV_LIB_A_RangeTo270History12, `PV_LIB_A_F6Data12, `PV_LIB_A_F6Arc12, `PV_LIB_A_F6History12, `PV_LIB_A_F6Constructors12, `PV_LIB_A_StoreActionTable12],
     #[`PV_LIB_A_RangeMatch12.quiet6, `PV_LIB_A_RangeMatch12.quiet7, `PV_LIB_A_RangeMatch12.trace, `PV_LIB_A_RangeMatch12.run, `PV_LIB_A_RangeCaptures12.sites, `PV_LIB_A_RangeCaptures12.break_quiet, `PV_LIB_A_RangeCaptures12.trace, `PV_LIB_A_RangeCaptures12.run, `PV_LIB_A_RangeReply12.returnedStore, `PV_LIB_A_RangeReply12.deliveredStore, `PV_LIB_A_RangeReply12.returned, `PV_LIB_A_RangeReply12.steps, `PV_LIB_A_RangeReply12.after, `PV_LIB_A_RangeReply12.run, `PV_LIB_A_RangeReply12.iterator, `PV_LIB_A_RangeHistory12.history, `PV_LIB_A_RangeHistory12.iterator, `PV_LIB_A_Continuation12.trace, `PV_LIB_A_Continuation12.run, `PV_LIB_A_ClosureAggregate12.trace, `PV_LIB_A_ClosureAggregate12.run, `PV_LIB_A_StructuredTrace12.issue_quiet, `PV_LIB_A_StructuredTrace12.enter_quiet, `PV_LIB_A_StructuredTrace12.trace, `PV_LIB_A_F166Chains12.prologue_sites, `PV_LIB_A_F166Chains12.prologue_trace, `PV_LIB_A_F166Chains12.prologue, `PV_LIB_A_F166Chains12.captures_sites, `PV_LIB_A_F166Chains12.captures_trace, `PV_LIB_A_F166Chains12.captures, `PV_LIB_A_SpawnEnter12.spawnPrograms, `PV_LIB_A_SpawnEnter12.spawn_trace, `PV_LIB_A_SpawnEnter12.spawn, `PV_LIB_A_SpawnEnter12.enter270Programs, `PV_LIB_A_SpawnEnter12.enter270_trace, `PV_LIB_A_SpawnEnter12.enter270, `PV_LIB_A_F166Builder12.waiting, `PV_LIB_A_F166Builder12.trace, `PV_LIB_A_F166Builder12.run, `PV_LIB_A_RangeInvariant12.Iterator, `PV_LIB_A_RangeInvariant12.next, `PV_LIB_A_RangeInvariant12.post, `PV_LIB_A_RangeInvariant12.prepared, `PV_LIB_A_RangeInvariant12.post_iterator, `PV_LIB_A_RangeInvariant12.poll, `PV_LIB_A_RangeInvariant12.delivered, `PV_LIB_A_F166History12.afterPrologue, `PV_LIB_A_F166History12.afterBuilder, `PV_LIB_A_F166History12.afterCaptures, `PV_LIB_A_F166History12.steps, `PV_LIB_A_F166History12.after, `PV_LIB_A_F166History12.run, `PV_LIB_A_SourceContinuation12.steps, `PV_LIB_A_SourceContinuation12.after, `PV_LIB_A_SourceContinuation12.run, `PV_LIB_A_Post93Prefix12.aggregateAfter, `PV_LIB_A_Post93Prefix12.spawnAfter, `PV_LIB_A_Post93Prefix12.steps, `PV_LIB_A_Post93Prefix12.after, `PV_LIB_A_Post93Prefix12.run, `PV_LIB_A_Post93Prefix12.retained, `PV_LIB_A_RangeTo270History12.history, `PV_LIB_A_F6Data12.source, `PV_LIB_A_F6Data12.finish, `PV_LIB_A_F6Data12.steps, `PV_LIB_A_F6Data12.after, `PV_LIB_A_F6Data12.trace, `PV_LIB_A_F6Data12.run, `PV_LIB_A_F6Arc12.shape, `PV_LIB_A_F6Arc12.sites, `PV_LIB_A_F6Arc12.storage, `PV_LIB_A_F6Arc12.waiting, `PV_LIB_A_F6Arc12.trace, `PV_LIB_A_F6Arc12.run, `PV_LIB_A_F6History12.afterData, `PV_LIB_A_F6History12.afterStorage, `PV_LIB_A_F6History12.steps, `PV_LIB_A_F6History12.after, `PV_LIB_A_F6History12.continuation, `PV_LIB_A_F6History12.history, `PV_LIB_A_F6Constructors12.entry121, `PV_LIB_A_F6Constructors12.entry123, `PV_LIB_A_F6Constructors12.counter, `PV_LIB_A_F6Constructors12.panicked, `PV_LIB_A_F6Constructors12.counter_word, `PV_LIB_A_F6Constructors12.panic_word, `PV_LIB_StoreActionTable.v2PrefixStep12, `PV_LIB_StoreActionTable.v2PrefixAdvance12, `PV_LIB_StoreActionTable.v2PrefixEntry12, `PV_LIB_StoreActionTable.prefix_step12])
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
        for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk,
          `PV_THR2_LibrarySemantics_AtomicUsizeNew.Returned.mk] do
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
