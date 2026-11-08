import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_F6SourceSequences14, `PV_LIB_A_F6Thread11, `PV_LIB_A_F6To15Fixed14, `PV_LIB_A_F6To220History14, `PV_LIB_A_FetchSubMachine10, `PV_LIB_A_FetchSubPrefixes10, `PV_LIB_A_FetchSubReply10, `PV_LIB_A_FetchSubRetry10, `PV_LIB_A_FetchSubSource10, `PV_LIB_A_FreeLifetime9, `PV_LIB_A_FrontierRun14, `PV_LIB_A_Full124TableGap14, `PV_LIB_A_GenericDropBinding, `PV_LIB_A_GenericDropMachine, `PV_LIB_A_GenericDropMachine9, `PV_LIB_A_GuardWeakBegin10, `PV_LIB_A_HistoryAny16, `PV_LIB_A_HistoryExtend16, `PV_LIB_A_IntrinsicInvoke13, `PV_LIB_A_LoopBackedge13, `PV_LIB_A_LoweredBody454, `PV_LIB_A_LoweredBody644, `PV_LIB_A_NameValidity, `PV_LIB_A_NativeCellFrame14, `PV_LIB_A_NativeFrontier14, `PV_LIB_A_NativeFull14, `PV_LIB_A_NativeLeaves, `PV_LIB_A_NextIteration13, `PV_LIB_A_Numbering, `PV_LIB_A_OperandFrame14, `PV_LIB_A_OptionDestruct157]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_F6SourceSequences14.offA, `PV_LIB_A_F6SourceSequences14.offB, `PV_LIB_A_F6SourceSequences14.offC, `PV_LIB_A_F6SourceSequences14.offD, `PV_LIB_A_F6SourceSequences14.offE, `PV_LIB_A_F6SourceSequences14.runA, `PV_LIB_A_F6SourceSequences14.runB, `PV_LIB_A_F6SourceSequences14.runC, `PV_LIB_A_F6SourceSequences14.runD, `PV_LIB_A_F6SourceSequences14.runE, `PV_LIB_A_F6SourceSequences14.shapeA, `PV_LIB_A_F6SourceSequences14.shapeB, `PV_LIB_A_F6SourceSequences14.shapeC, `PV_LIB_A_F6SourceSequences14.shapeD, `PV_LIB_A_F6SourceSequences14.shapeE, `PV_LIB_A_F6Thread11.call_quiet, `PV_LIB_A_F6Thread11.issue, `PV_LIB_A_F6Thread11.poll, `PV_LIB_A_F6Thread11.segment3, `PV_LIB_A_F6Thread11.storage, `PV_LIB_A_F6Thread11.wait_quiet, `PV_LIB_A_F6To15Fixed14.certified, `PV_LIB_A_F6To15Fixed14.history, `PV_LIB_A_F6To15Fixed14.route, `PV_LIB_A_F6To15Fixed14.segments, `PV_LIB_A_F6To220History14.continuation, `PV_LIB_A_F6To220History14.fallback, `PV_LIB_A_F6To220History14.history, `PV_LIB_A_FetchSubMachine10.agreement, `PV_LIB_A_FetchSubMachine10.gap, `PV_LIB_A_FetchSubMachine10.poll, `PV_LIB_A_FetchSubMachine10.retained, `PV_LIB_A_FetchSubMachine10.step, `PV_LIB_A_FetchSubMachine10.wrap, `PV_LIB_A_FetchSubPrefixes10.advance, `PV_LIB_A_FetchSubPrefixes10.build_run, `PV_LIB_A_FetchSubPrefixes10.guard_run, `PV_LIB_A_FetchSubPrefixes10.nonwaiting, `PV_LIB_A_FetchSubReply10.PV_THR2_LibrarySemantics_FetchSubValue581, `PV_LIB_A_FetchSubReply10.at_request, `PV_LIB_A_FetchSubReply10.away, `PV_LIB_A_FetchSubReply10.effects, `PV_LIB_A_FetchSubReply10.handler, `PV_LIB_A_FetchSubReply10.non_success, `PV_LIB_A_FetchSubReply10.pending, `PV_LIB_A_FetchSubReply10.readOld, `PV_LIB_A_FetchSubReply10.returned, `PV_LIB_A_FetchSubReply10.selected, `PV_LIB_A_FetchSubRetry10.begin, `PV_LIB_A_FetchSubRetry10.graph, `PV_LIB_A_FetchSubRetry10.pending, `PV_LIB_A_FetchSubSource10.atomic_root_read, `PV_LIB_A_FetchSubSource10.read_source, `PV_LIB_A_FetchSubSource10.same_write, `PV_LIB_A_FreeLifetime9.old_world_unchanged, `PV_LIB_A_FreeLifetime9.primitive_non_success, `PV_LIB_A_FreeLifetime9.primitive_success, `PV_LIB_A_FrontierRun14.run, `PV_LIB_A_Full124TableGap14.at124, `PV_LIB_A_Full124TableGap14.not_prefix_tables, `PV_LIB_A_GenericDropBinding.arc, `PV_LIB_A_GenericDropBinding.away, `PV_LIB_A_GenericDropBinding.bind, `PV_LIB_A_GenericDropBinding.exact]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_GenericDropBinding.hooks, `PV_LIB_A_GenericDropBinding.normalized, `PV_LIB_A_GenericDropBinding.programs, `PV_LIB_A_GenericDropBinding.resolveToken, `PV_LIB_A_GenericDropBinding.selected, `PV_LIB_A_GenericDropBinding.slow, `PV_LIB_A_GenericDropBinding.weakGuard, `PV_LIB_A_GenericDropMachine.agreement, `PV_LIB_A_GenericDropMachine.noop, `PV_LIB_A_GenericDropMachine.phase, `PV_LIB_A_GenericDropMachine.selectDrop, `PV_LIB_A_GenericDropMachine.step, `PV_LIB_A_GenericDropMachine.unitTag, `PV_LIB_A_GenericDropMachine9.agreement, `PV_LIB_A_GenericDropMachine9.phase, `PV_LIB_A_GenericDropMachine9.resolution, `PV_LIB_A_GenericDropMachine9.resolution248, `PV_LIB_A_GenericDropMachine9.select248, `PV_LIB_A_GenericDropMachine9.selectCell, `PV_LIB_A_GenericDropMachine9.selectDrop, `PV_LIB_A_GenericDropMachine9.step, `PV_LIB_A_GuardWeakBegin10.begin, `PV_LIB_A_GuardWeakBegin10.pointer, `PV_LIB_A_HistoryAny16.extend, `PV_LIB_A_HistoryExtend16.extend, `PV_LIB_A_IntrinsicInvoke13.actual, `PV_LIB_A_IntrinsicInvoke13.quiet, `PV_LIB_A_IntrinsicInvoke13.run, `PV_LIB_A_LoopBackedge13.continue_quiet, `PV_LIB_A_LoopBackedge13.cost, `PV_LIB_A_LoopBackedge13.keeps_iterator, `PV_LIB_A_LoopBackedge13.off, `PV_LIB_A_LoopBackedge13.run, `PV_LIB_A_LoopBackedge13.shape, `PV_LIB_A_LoweredBody454.instantiate, `PV_LIB_A_LoweredBody454.program, `PV_LIB_A_LoweredBody644.instantiate, `PV_LIB_A_LoweredBody644.program, `PV_LIB_A_NameValidity.none_entry, `PV_LIB_A_NameValidity.some_entry, `PV_LIB_A_NativeCellFrame14.full_reply, `PV_LIB_A_NativeCellFrame14.issued, `PV_LIB_A_NativeCellFrame14.returned_store, `PV_LIB_A_NativeFrontier14.after, `PV_LIB_A_NativeFrontier14.run, `PV_LIB_A_NativeFrontier14.steps, `PV_LIB_A_NativeFull14.exact_call, `PV_LIB_A_NativeLeaves.certified277, `PV_LIB_A_NativeLeaves.certified278, `PV_LIB_A_NativeLeaves.certified279, `PV_LIB_A_NativeLeaves.certified280, `PV_LIB_A_NativeLeaves.certified612, `PV_LIB_A_NextIteration13.history, `PV_LIB_A_Numbering.child_entry, `PV_LIB_A_Numbering.lower_bound, `PV_LIB_A_Numbering.original_entry, `PV_LIB_A_OperandFrame14.Safe, `PV_LIB_A_OperandFrame14.operand_frame, `PV_LIB_A_OperandFrame14.operands_frame, `PV_LIB_A_OptionDestruct157.PV_THR2_LibrarySemantics_OptionDestruct157, `PV_LIB_A_OptionDestruct157.branches]
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
