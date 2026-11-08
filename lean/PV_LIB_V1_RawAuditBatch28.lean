import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_F166Whole, `PV_LIB_SPEC_StackReferenceGap12, `PV_LIB_SPEC_StackSize14, `PV_LIB_SPEC_Success13, `PV_LIB_SPEC_SuccessResources, `PV_LIB_SPEC_SuccessSchedule12, `PV_LIB_SPEC_ThreadContract, `PV_LIB_SPEC_ThreadId13, `PV_LIB_SPEC_ThreadMachine, `PV_LIB_SPEC_ThreadNewNative, `PV_LIB_SPEC_ThreadNewRecheck12, `PV_LIB_SPEC_ThreadRepresentationGap, `PV_LIB_SPEC_ThreadWordRecheck12, `PV_LIB_SPEC_ThreadWords12, `PV_LIB_SPEC_Tls18Bound16, `PV_LIB_SPEC_Tls18Delivery16, `PV_LIB_SPEC_Tls18Reached16, `PV_LIB_SPEC_Tls277Bound15, `PV_LIB_SPEC_Tls277Delivery15, `PV_LIB_SPEC_Tls277Native15, `PV_LIB_SPEC_Tls277Request15, `PV_LIB_SPEC_Tls277Route15, `PV_LIB_SPEC_Tls278Bound15]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_StackReferenceGap12.reference, `PV_LIB_SPEC_StackReferenceGap12.store, `PV_LIB_SPEC_StackReferenceGap12.unregistered, `PV_LIB_SPEC_StackSize14.cached, `PV_LIB_SPEC_StackSize14.closureKind, `PV_LIB_SPEC_StackSize14.minimumOffset, `PV_LIB_SPEC_StackSize14.other, `PV_LIB_SPEC_StackSize14.reply, `PV_LIB_SPEC_StackSize14.token, `PV_LIB_SPEC_StackSize14.value, `PV_LIB_SPEC_Success13.allocations, `PV_LIB_SPEC_Success13.environment, `PV_LIB_SPEC_Success13.native, `PV_LIB_SPEC_Success13.parameters, `PV_LIB_SPEC_Success13.pre, `PV_LIB_SPEC_SuccessResources.allocation, `PV_LIB_SPEC_SuccessResources.callback, `PV_LIB_SPEC_SuccessResources.callbackResources, `PV_LIB_SPEC_SuccessResources.init, `PV_LIB_SPEC_SuccessResources.initResources, `PV_LIB_SPEC_SuccessResources.local_callback, `PV_LIB_SPEC_SuccessResources.local_init, `PV_LIB_SPEC_SuccessResources.packet, `PV_LIB_SPEC_SuccessSchedule12.allocation, `PV_LIB_SPEC_SuccessSchedule12.allocation_reply, `PV_LIB_SPEC_SuccessSchedule12.entry, `PV_LIB_SPEC_SuccessSchedule12.environment, `PV_LIB_SPEC_SuccessSchedule12.native, `PV_LIB_SPEC_SuccessSchedule12.parameters, `PV_LIB_SPEC_SuccessSchedule12.pointer, `PV_LIB_SPEC_SuccessSchedule12.replies, `PV_LIB_SPEC_ThreadContract.BehavioralPost, `PV_LIB_SPEC_ThreadContract.Boundary, `PV_LIB_SPEC_ThreadContract.ConsumedPending, `PV_LIB_SPEC_ThreadContract.Diverges, `PV_LIB_SPEC_ThreadContract.First, `PV_LIB_SPEC_ThreadContract.Numbered, `PV_LIB_SPEC_ThreadContract.Observation, `PV_LIB_SPEC_ThreadContract.OwnComplete, `PV_LIB_SPEC_ThreadContract.SourceAdequacy, `PV_LIB_SPEC_ThreadContract.Terminal, `PV_LIB_SPEC_ThreadContract.abort_prefix, `PV_LIB_SPEC_ThreadContract.configView, `PV_LIB_SPEC_ThreadContract.counter_irrelevant, `PV_LIB_SPEC_ThreadContract.observe, `PV_LIB_SPEC_ThreadContract.reference, `PV_LIB_SPEC_ThreadContract.statusView, `PV_LIB_SPEC_ThreadContract.storeView, `PV_LIB_SPEC_ThreadId13.counterOffset, `PV_LIB_SPEC_ThreadId13.other, `PV_LIB_SPEC_ThreadId13.reply, `PV_LIB_SPEC_ThreadId13.stored_counter, `PV_LIB_SPEC_ThreadId13.successful_ghost, `PV_LIB_SPEC_ThreadId13.value, `PV_LIB_SPEC_ThreadMachine.Event, `PV_LIB_SPEC_ThreadMachine.Machine, `PV_LIB_SPEC_ThreadMachine.ReachedAgreement, `PV_LIB_SPEC_ThreadMachine.SourceAdequacy, `PV_LIB_SPEC_ThreadMachine.State, `PV_LIB_SPEC_ThreadMachine.away, `PV_LIB_SPEC_ThreadMachine.registration, `PV_LIB_SPEC_ThreadMachine.run, `PV_LIB_SPEC_ThreadMachine.step, `PV_LIB_SPEC_ThreadMachine.writer]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_ThreadNewNative.ghost_frame, `PV_LIB_SPEC_ThreadNewNative.operands, `PV_LIB_SPEC_ThreadNewNative.rawReply, `PV_LIB_SPEC_ThreadNewNative.reply, `PV_LIB_SPEC_ThreadNewNative.shape, `PV_LIB_SPEC_ThreadNewRecheck12.sparse_stores, `PV_LIB_SPEC_ThreadNewRecheck12.success, `PV_LIB_SPEC_ThreadRepresentationGap.incompatible, `PV_LIB_SPEC_ThreadRepresentationGap.scope_handler, `PV_LIB_SPEC_ThreadRepresentationGap.shaped_thread, `PV_LIB_SPEC_ThreadRepresentationGap.thread_word, `PV_LIB_SPEC_ThreadRow.Frame, `PV_LIB_SPEC_ThreadRow.FrameComparison, `PV_LIB_SPEC_ThreadRow.Post, `PV_LIB_SPEC_ThreadWordRecheck12.count_word, `PV_LIB_SPEC_ThreadWordRecheck12.current_success, `PV_LIB_SPEC_ThreadWordRecheck12.increment_written, `PV_LIB_SPEC_ThreadWordRecheck12.inner, `PV_LIB_SPEC_ThreadWordRecheck12.one, `PV_LIB_SPEC_ThreadWordRecheck12.prepared, `PV_LIB_SPEC_ThreadWordRecheck12.read_away, `PV_LIB_SPEC_ThreadWordRecheck12.returned_thread_shape, `PV_LIB_SPEC_ThreadWordRecheck12.tls_word, `PV_LIB_SPEC_ThreadWords12.Pointer, `PV_LIB_SPEC_ThreadWords12.clone, `PV_LIB_SPEC_ThreadWords12.current, `PV_LIB_SPEC_ThreadWords12.current_other, `PV_LIB_SPEC_ThreadWords12.ghost_write, `PV_LIB_SPEC_ThreadWords12.increment, `PV_LIB_SPEC_ThreadWords12.read, `PV_LIB_SPEC_ThreadWords12.read_written, `PV_LIB_SPEC_ThreadWords12.wordImage, `PV_LIB_SPEC_ThreadWords12.write, `PV_LIB_SPEC_Tls18Bound16.answer, `PV_LIB_SPEC_Tls18Bound16.arguments, `PV_LIB_SPEC_Tls18Bound16.different, `PV_LIB_SPEC_Tls18Bound16.request, `PV_LIB_SPEC_Tls18Bound16.selected, `PV_LIB_SPEC_Tls18Bound16.token, `PV_LIB_SPEC_Tls18Bound16.trigger, `PV_LIB_SPEC_Tls18Delivery16.lookup, `PV_LIB_SPEC_Tls18Delivery16.transition, `PV_LIB_SPEC_Tls18Reached16.active, `PV_LIB_SPEC_Tls18Reached16.reached, `PV_LIB_SPEC_Tls18Reached16.read_nil, `PV_LIB_SPEC_Tls18Reached16.source, `PV_LIB_SPEC_Tls277Bound15.answer, `PV_LIB_SPEC_Tls277Bound15.trigger, `PV_LIB_SPEC_Tls277Delivery15.transition, `PV_LIB_SPEC_Tls277Native15.different, `PV_LIB_SPEC_Tls277Native15.native, `PV_LIB_SPEC_Tls277Native15.pointer, `PV_LIB_SPEC_Tls277Native15.pure, `PV_LIB_SPEC_Tls277Native15.token, `PV_LIB_SPEC_Tls277Native15.value, `PV_LIB_SPEC_Tls277Request15.after, `PV_LIB_SPEC_Tls277Request15.request, `PV_LIB_SPEC_Tls277Request15.site, `PV_LIB_SPEC_Tls277Route15.route, `PV_LIB_SPEC_Tls278Bound15.answer, `PV_LIB_SPEC_Tls278Bound15.different]
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
