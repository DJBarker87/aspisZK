import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_CallbackBindings14, `PV_LIB_A_CallbackTail14, `PV_LIB_A_FrontierRun14, `PV_LIB_A_F219Selected14, `PV_LIB_A_F219Enter31614, `PV_LIB_A_F219CallbackHistory14, `PV_LIB_A_F6CallbackHistory14, `PV_LIB_A_F6To220History14, `PV_LIB_A_F220Prefix14, `PV_LIB_A_F220Enter20814, `PV_LIB_A_F208Prefix14, `PV_LIB_A_OwnerTableCongruence14, `PV_LIB_A_SourceSelectCongruence14, `PV_LIB_A_TableCongruence14, `PV_LIB_A_NativeFull14, `PV_LIB_A_NativeFrontier14, `PV_LIB_A_PrefixNativeCalls14, `PV_LIB_A_F219Enter316Any14, `PV_LIB_A_F6SourceSequences14, `PV_LIB_A_PrefixStructuredCalls14, `PV_LIB_A_PrefixComposition14, `PV_LIB_A_F6To15Fixed14, `PV_LIB_A_SourceCellFrame14, `PV_LIB_A_OperandFrame14, `PV_LIB_A_ExpressionFrame14, `PV_LIB_A_SequenceFrame14, `PV_LIB_A_NativeCellFrame14, `PV_LIB_A_PrefixSequenceFrames14, `PV_LIB_A_V2Neutral14, `PV_LIB_A_V2TraceTransport14, `PV_LIB_A_V2Frontiers14, `PV_LIB_A_V2NativeFrontier14, `PV_LIB_A_V2PrefixTables14, `PV_LIB_A_V2PrefixBindings14, `PV_LIB_A_V2Composition14, `PV_LIB_A_V2Callback14, `PV_LIB_A_V2ActualBindings14, `PV_LIB_A_Full124TableGap14, `PV_LIB_A_V2F124Entry14, `PV_LIB_A_F124EntryData14, `PV_LIB_A_V2F6To12414, `PV_LIB_A_ScopePayloadShape14, `PV_LIB_A_ScopeIncrementShape14, `PV_LIB_A_V2Post124To15, `PV_LIB_A_ScopePayloadIdentityGap14, `PV_LIB_A_F124ReturnedFrame14],
     #[`PV_LIB_A_CallbackBindings14.unary, `PV_LIB_A_CallbackBindings14.callback, `PV_LIB_A_CallbackBindings14.pointer, `PV_LIB_A_CallbackTail14.shape, `PV_LIB_A_CallbackTail14.result, `PV_LIB_A_CallbackTail14.cost, `PV_LIB_A_CallbackTail14.cells, `PV_LIB_A_FrontierRun14.run, `PV_LIB_A_F219Selected14.operands, `PV_LIB_A_F219Selected14.selected, `PV_LIB_A_F219Selected14.issue, `PV_LIB_A_F219Selected14.invoke, `PV_LIB_A_F219Enter31614.finish, `PV_LIB_A_F219Enter31614.exact_tail, `PV_LIB_A_F219Enter31614.run, `PV_LIB_A_F219CallbackHistory14.shape, `PV_LIB_A_F219CallbackHistory14.off, `PV_LIB_A_F219CallbackHistory14.after, `PV_LIB_A_F219CallbackHistory14.steps, `PV_LIB_A_F219CallbackHistory14.run, `PV_LIB_A_F6CallbackHistory14.steps, `PV_LIB_A_F6CallbackHistory14.stage7, `PV_LIB_A_F6CallbackHistory14.continuation, `PV_LIB_A_F6CallbackHistory14.history, `PV_LIB_A_F6To220History14.fallback, `PV_LIB_A_F6To220History14.continuation, `PV_LIB_A_F6To220History14.history, `PV_LIB_A_F220Prefix14.shape, `PV_LIB_A_F220Prefix14.off, `PV_LIB_A_F220Prefix14.run, `PV_LIB_A_F220Enter20814.programs, `PV_LIB_A_F220Enter20814.shape, `PV_LIB_A_F220Enter20814.steps, `PV_LIB_A_F220Enter20814.after, `PV_LIB_A_F220Enter20814.run, `PV_LIB_A_F208Prefix14.shape, `PV_LIB_A_F208Prefix14.off, `PV_LIB_A_F208Prefix14.run, `PV_LIB_A_OwnerTableCongruence14.uniform, `PV_LIB_A_OwnerTableCongruence14.operator, `PV_LIB_A_OwnerTableCongruence14.owner, `PV_LIB_A_SourceSelectCongruence14.select, `PV_LIB_A_TableCongruence14.source, `PV_LIB_A_TableCongruence14.step, `PV_LIB_A_NativeFull14.exact_call, `PV_LIB_A_NativeFrontier14.steps, `PV_LIB_A_NativeFrontier14.after, `PV_LIB_A_NativeFrontier14.run, `PV_LIB_A_PrefixNativeCalls14.shape121, `PV_LIB_A_PrefixNativeCalls14.child121, `PV_LIB_A_PrefixNativeCalls14.run121, `PV_LIB_A_PrefixNativeCalls14.shape122, `PV_LIB_A_PrefixNativeCalls14.child122, `PV_LIB_A_PrefixNativeCalls14.run122, `PV_LIB_A_PrefixNativeCalls14.shape123, `PV_LIB_A_PrefixNativeCalls14.child123, `PV_LIB_A_PrefixNativeCalls14.run123, `PV_LIB_A_PrefixNativeCalls14.shape124, `PV_LIB_A_PrefixNativeCalls14.child124, `PV_LIB_A_PrefixNativeCalls14.run124, `PV_LIB_A_PrefixNativeCalls14.shape134, `PV_LIB_A_PrefixNativeCalls14.child134, `PV_LIB_A_PrefixNativeCalls14.run134, `PV_LIB_A_PrefixNativeCalls14.shape410, `PV_LIB_A_PrefixNativeCalls14.child410, `PV_LIB_A_PrefixNativeCalls14.run410, `PV_LIB_A_F219Enter316Any14.issue, `PV_LIB_A_F219Enter316Any14.exact_tail, `PV_LIB_A_F219Enter316Any14.run, `PV_LIB_A_F6SourceSequences14.shapeA, `PV_LIB_A_F6SourceSequences14.offA, `PV_LIB_A_F6SourceSequences14.runA, `PV_LIB_A_F6SourceSequences14.shapeB, `PV_LIB_A_F6SourceSequences14.offB, `PV_LIB_A_F6SourceSequences14.runB, `PV_LIB_A_F6SourceSequences14.shapeC, `PV_LIB_A_F6SourceSequences14.offC, `PV_LIB_A_F6SourceSequences14.runC, `PV_LIB_A_F6SourceSequences14.shapeD, `PV_LIB_A_F6SourceSequences14.offD, `PV_LIB_A_F6SourceSequences14.runD, `PV_LIB_A_F6SourceSequences14.shapeE, `PV_LIB_A_F6SourceSequences14.offE, `PV_LIB_A_F6SourceSequences14.runE, `PV_LIB_A_PrefixStructuredCalls14.shape125, `PV_LIB_A_PrefixStructuredCalls14.lookup125, `PV_LIB_A_PrefixStructuredCalls14.run125, `PV_LIB_A_PrefixStructuredCalls14.shape219, `PV_LIB_A_PrefixStructuredCalls14.lookup219, `PV_LIB_A_PrefixStructuredCalls14.run219, `PV_LIB_A_PrefixStructuredCalls14.shape220, `PV_LIB_A_PrefixStructuredCalls14.lookup220, `PV_LIB_A_PrefixStructuredCalls14.run220, `PV_LIB_A_PrefixStructuredCalls14.shape208, `PV_LIB_A_PrefixStructuredCalls14.lookup208, `PV_LIB_A_PrefixStructuredCalls14.run208, `PV_LIB_A_PrefixStructuredCalls14.shape15, `PV_LIB_A_PrefixStructuredCalls14.lookup15, `PV_LIB_A_PrefixStructuredCalls14.run15, `PV_LIB_A_PrefixComposition14.lift, `PV_LIB_A_PrefixComposition14.join, `PV_LIB_A_PrefixComposition14.chain, `PV_LIB_A_PrefixComposition14.lifted, `PV_LIB_A_PrefixComposition14.joined, `PV_LIB_A_PrefixComposition14.chained, `PV_LIB_A_F6To15Fixed14.segments, `PV_LIB_A_F6To15Fixed14.route, `PV_LIB_A_F6To15Fixed14.certified, `PV_LIB_A_F6To15Fixed14.history, `PV_LIB_A_SourceCellFrame14.Below, `PV_LIB_A_SourceCellFrame14.refl, `PV_LIB_A_SourceCellFrame14.trans, `PV_LIB_A_SourceCellFrame14.located, `PV_LIB_A_SourceCellFrame14.write_frame, `PV_LIB_A_SourceCellFrame14.writeAddress_frame, `PV_LIB_A_OperandFrame14.Safe, `PV_LIB_A_OperandFrame14.operand_frame, `PV_LIB_A_OperandFrame14.operands_frame, `PV_LIB_A_ExpressionFrame14.Safe, `PV_LIB_A_ExpressionFrame14.evaluate_frame, `PV_LIB_A_ExpressionFrame14.bind_frame, `PV_LIB_A_SequenceFrame14.bound_frame, `PV_LIB_A_SequenceFrame14.storeOf, `PV_LIB_A_SequenceFrame14.Safe, `PV_LIB_A_SequenceFrame14.result_frame, `PV_LIB_A_NativeCellFrame14.issued, `PV_LIB_A_NativeCellFrame14.returned_store, `PV_LIB_A_NativeCellFrame14.full_reply, `PV_LIB_A_PrefixSequenceFrames14.safe0, `PV_LIB_A_PrefixSequenceFrames14.safe1, `PV_LIB_A_PrefixSequenceFrames14.safe2, `PV_LIB_A_PrefixSequenceFrames14.safe3, `PV_LIB_A_PrefixSequenceFrames14.safe4, `PV_LIB_A_PrefixSequenceFrames14.safe5, `PV_LIB_A_PrefixSequenceFrames14.safe6, `PV_LIB_A_PrefixSequenceFrames14.safe7, `PV_LIB_A_PrefixSequenceFrames14.safe8, `PV_LIB_A_PrefixSequenceFrames14.safe9, `PV_LIB_A_PrefixSequenceFrames14.safe10, `PV_LIB_A_PrefixSequenceFrames14.safe11, `PV_LIB_A_PrefixSequenceFrames14.safe12, `PV_LIB_A_PrefixSequenceFrames14.iterator, `PV_LIB_A_V2Neutral14.table_none, `PV_LIB_A_V2Neutral14.select_none, `PV_LIB_A_V2Neutral14.neutral, `PV_LIB_A_V2Neutral14.successor_step, `PV_LIB_A_V2TraceTransport14.step, `PV_LIB_A_V2TraceTransport14.run, `PV_LIB_A_V2TraceTransport14.successor, `PV_LIB_A_V2Frontiers14.run, `PV_LIB_A_V2Frontiers14.sequence, `PV_LIB_A_V2Frontiers14.issue, `PV_LIB_A_V2Frontiers14.structured, `PV_LIB_A_V2NativeFrontier14.trace, `PV_LIB_A_V2NativeFrontier14.run, `PV_LIB_A_V2PrefixTables14.Tables, `PV_LIB_A_V2PrefixTables14.installed, `PV_LIB_A_V2PrefixBindings14.run121, `PV_LIB_A_V2PrefixBindings14.run122, `PV_LIB_A_V2PrefixBindings14.run123, `PV_LIB_A_V2PrefixBindings14.run124, `PV_LIB_A_V2PrefixBindings14.run134, `PV_LIB_A_V2PrefixBindings14.run410, `PV_LIB_A_V2PrefixBindings14.run125, `PV_LIB_A_V2PrefixBindings14.run219, `PV_LIB_A_V2PrefixBindings14.run220, `PV_LIB_A_V2PrefixBindings14.run208, `PV_LIB_A_V2PrefixBindings14.run15, `PV_LIB_A_V2Composition14.advance_add, `PV_LIB_A_V2Composition14.join, `PV_LIB_A_V2Composition14.chain, `PV_LIB_A_V2Composition14.joined, `PV_LIB_A_V2Composition14.chained, `PV_LIB_A_V2Callback14.issue, `PV_LIB_A_V2Callback14.invoke, `PV_LIB_A_V2Callback14.exact_tail, `PV_LIB_A_V2Callback14.run, `PV_LIB_A_V2ActualBindings14.run121, `PV_LIB_A_V2ActualBindings14.run122, `PV_LIB_A_V2ActualBindings14.run123, `PV_LIB_A_V2ActualBindings14.run124, `PV_LIB_A_V2ActualBindings14.run134, `PV_LIB_A_V2ActualBindings14.run410, `PV_LIB_A_V2ActualBindings14.run125, `PV_LIB_A_V2ActualBindings14.run219, `PV_LIB_A_V2ActualBindings14.run220, `PV_LIB_A_V2ActualBindings14.run208, `PV_LIB_A_V2ActualBindings14.run15, `PV_LIB_A_Full124TableGap14.at124, `PV_LIB_A_Full124TableGap14.not_prefix_tables, `PV_LIB_A_V2F124Entry14.run, `PV_LIB_A_V2F124Entry14.numbered, `PV_LIB_A_F124EntryData14.provenance, `PV_LIB_A_F124EntryData14.valid, `PV_LIB_A_F124EntryData14.bounded, `PV_LIB_A_F124EntryData14.pre, `PV_LIB_A_F124EntryData14.installed, `PV_LIB_A_V2F6To12414.full_tables, `PV_LIB_A_V2F6To12414.segments, `PV_LIB_A_V2F6To12414.route, `PV_LIB_A_V2F6To12414.certified, `PV_LIB_A_V2F6To12414.history, `PV_LIB_A_ScopePayloadShape14.reference, `PV_LIB_A_ScopePayloadShape14.read_count, `PV_LIB_A_ScopePayloadShape14.replace_count, `PV_LIB_A_ScopePayloadShape14.overwrite, `PV_LIB_A_ScopePayloadShape14.write_count, `PV_LIB_A_ScopeIncrementShape14.zero_increment, `PV_LIB_A_ScopeIncrementShape14.increment, `PV_LIB_A_V2Post124To15.segments, `PV_LIB_A_V2Post124To15.route, `PV_LIB_A_V2Post124To15.certified, `PV_LIB_A_V2Post124To15.history, `PV_LIB_A_ScopePayloadIdentityGap14.initial, `PV_LIB_A_ScopePayloadIdentityGap14.not_fixed_payload, `PV_LIB_A_ScopePayloadIdentityGap14.checked, `PV_LIB_A_F124ReturnedFrame14.source_frame, `PV_LIB_A_F124ReturnedFrame14.counter_mono, `PV_LIB_A_F124ReturnedFrame14.stack_numbering, `PV_LIB_A_F124ReturnedFrame14.numbered, `PV_LIB_A_F124ReturnedFrame14.post_and_frame])
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
