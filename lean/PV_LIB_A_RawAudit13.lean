import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_SourceSequence13, `PV_LIB_A_SequenceFrontier13, `PV_LIB_A_F6Captures13, `PV_LIB_A_StructuredFrontier13, `PV_LIB_A_CallFrame13, `PV_LIB_A_Continue13, `PV_LIB_A_LoopBackedge13, `PV_LIB_A_F6Enter12513, `PV_LIB_A_F125Prologue13, `PV_LIB_A_F125Enter21913, `PV_LIB_A_F219Prologue13, `PV_LIB_A_F219Full13413, `PV_LIB_A_F219To31813, `PV_LIB_A_RangeIteration13, `PV_LIB_A_F6CatchHistory13, `PV_LIB_A_CallIssue13, `PV_LIB_A_F219Issue31813, `PV_LIB_A_IntrinsicInvoke13, `PV_LIB_A_F316Prefix13, `PV_LIB_A_F316Full41013, `PV_LIB_A_F316ToInvoke13, `PV_LIB_A_F316Enter22013, `PV_LIB_A_F6IssuedHistory13, `PV_LIB_A_F316History13, `PV_LIB_A_CallNumbers13, `PV_LIB_A_NextIteration13, `PV_LIB_A_StoreActionTable13],
     #[`PV_LIB_A_SourceSequence13.aggregate_quiet, `PV_LIB_A_SourceSequence13.certified, `PV_LIB_A_SourceSequence13.run, `PV_LIB_A_SequenceFrontier13.prepend, `PV_LIB_A_SequenceFrontier13.cost, `PV_LIB_A_SequenceFrontier13.finish, `PV_LIB_A_SequenceFrontier13.steps, `PV_LIB_A_SequenceFrontier13.after, `PV_LIB_A_SequenceFrontier13.run, `PV_LIB_A_F6Captures13.shape, `PV_LIB_A_F6Captures13.off, `PV_LIB_A_F6Captures13.steps, `PV_LIB_A_F6Captures13.after, `PV_LIB_A_F6Captures13.run, `PV_LIB_A_StructuredFrontier13.source, `PV_LIB_A_StructuredFrontier13.fn, `PV_LIB_A_StructuredFrontier13.node, `PV_LIB_A_StructuredFrontier13.cost, `PV_LIB_A_StructuredFrontier13.finish, `PV_LIB_A_StructuredFrontier13.steps, `PV_LIB_A_StructuredFrontier13.after, `PV_LIB_A_StructuredFrontier13.run, `PV_LIB_A_CallFrame13.arguments_frame, `PV_LIB_A_CallFrame13.issued_frame, `PV_LIB_A_CallFrame13.entered_iterator, `PV_LIB_A_CallFrame13.returned_iterator, `PV_LIB_A_Continue13.run, `PV_LIB_A_LoopBackedge13.shape, `PV_LIB_A_LoopBackedge13.off, `PV_LIB_A_LoopBackedge13.cost, `PV_LIB_A_LoopBackedge13.keeps_iterator, `PV_LIB_A_LoopBackedge13.continue_quiet, `PV_LIB_A_LoopBackedge13.run, `PV_LIB_A_F6Enter12513.programs, `PV_LIB_A_F6Enter12513.shape, `PV_LIB_A_F6Enter12513.steps, `PV_LIB_A_F6Enter12513.after, `PV_LIB_A_F6Enter12513.run, `PV_LIB_A_F125Prologue13.shape, `PV_LIB_A_F125Prologue13.off, `PV_LIB_A_F125Prologue13.steps, `PV_LIB_A_F125Prologue13.after, `PV_LIB_A_F125Prologue13.run, `PV_LIB_A_F125Enter21913.programs, `PV_LIB_A_F125Enter21913.shape, `PV_LIB_A_F125Enter21913.steps, `PV_LIB_A_F125Enter21913.after, `PV_LIB_A_F125Enter21913.run, `PV_LIB_A_F219Prologue13.shape, `PV_LIB_A_F219Prologue13.off, `PV_LIB_A_F219Prologue13.steps, `PV_LIB_A_F219Prologue13.after, `PV_LIB_A_F219Prologue13.run, `PV_LIB_A_F219Full13413.source, `PV_LIB_A_F219Full13413.waiting, `PV_LIB_A_F219Full13413.trace, `PV_LIB_A_F219Full13413.run, `PV_LIB_A_F219To31813.shape, `PV_LIB_A_F219To31813.off, `PV_LIB_A_F219To31813.steps, `PV_LIB_A_F219To31813.after, `PV_LIB_A_F219To31813.run, `PV_LIB_A_RangeIteration13.prepared, `PV_LIB_A_RangeIteration13.history, `PV_LIB_A_F6CatchHistory13.steps, `PV_LIB_A_F6CatchHistory13.stage7, `PV_LIB_A_F6CatchHistory13.continuation, `PV_LIB_A_F6CatchHistory13.history, `PV_LIB_A_CallIssue13.steps, `PV_LIB_A_CallIssue13.finish, `PV_LIB_A_CallIssue13.after, `PV_LIB_A_CallIssue13.run, `PV_LIB_A_F219Issue31813.programs, `PV_LIB_A_F219Issue31813.shape, `PV_LIB_A_F219Issue31813.steps, `PV_LIB_A_F219Issue31813.after, `PV_LIB_A_F219Issue31813.run, `PV_LIB_A_IntrinsicInvoke13.quiet, `PV_LIB_A_IntrinsicInvoke13.run, `PV_LIB_A_IntrinsicInvoke13.actual, `PV_LIB_A_F316Prefix13.shape, `PV_LIB_A_F316Prefix13.off, `PV_LIB_A_F316Prefix13.steps, `PV_LIB_A_F316Prefix13.after, `PV_LIB_A_F316Prefix13.run, `PV_LIB_A_F316Full41013.source, `PV_LIB_A_F316Full41013.waiting, `PV_LIB_A_F316Full41013.trace, `PV_LIB_A_F316Full41013.run, `PV_LIB_A_F316ToInvoke13.shape, `PV_LIB_A_F316ToInvoke13.off, `PV_LIB_A_F316ToInvoke13.steps, `PV_LIB_A_F316ToInvoke13.after, `PV_LIB_A_F316ToInvoke13.run, `PV_LIB_A_F316Enter22013.programs, `PV_LIB_A_F316Enter22013.shape, `PV_LIB_A_F316Enter22013.steps, `PV_LIB_A_F316Enter22013.after, `PV_LIB_A_F316Enter22013.run, `PV_LIB_A_F6IssuedHistory13.steps, `PV_LIB_A_F6IssuedHistory13.after, `PV_LIB_A_F6IssuedHistory13.continuation, `PV_LIB_A_F6IssuedHistory13.history, `PV_LIB_A_F316History13.steps, `PV_LIB_A_F316History13.stage4, `PV_LIB_A_F316History13.run, `PV_LIB_A_CallNumbers13.arguments_counter, `PV_LIB_A_CallNumbers13.issued_counter, `PV_LIB_A_CallNumbers13.push_bounds, `PV_LIB_A_NextIteration13.history, `PV_LIB_StoreActionTable.v2PrefixStep13, `PV_LIB_StoreActionTable.v2PrefixAdvance13, `PV_LIB_StoreActionTable.prefix_step13])
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
