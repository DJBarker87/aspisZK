import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_NativeKinds, `PV_LIB_SPEC_AtomicBoolGap, `PV_LIB_SPEC_NativeBoolArc, `PV_LIB_SPEC_NativeConstructors, `PV_LIB_SPEC_ThreadNewNative, `PV_LIB_SPEC_NativeBoolRuntime, `PV_LIB_SPEC_SuccessSchedule12, `PV_LIB_SPEC_NativeBindings12, `PV_LIB_SPEC_ThreadNewRecheck12, `PV_LIB_SPEC_NativeRecheck12, `PV_LIB_SPEC_StackReferenceGap12, `PV_LIB_SPEC_PhysicalStack12, `PV_LIB_SPEC_StackCallback12, `PV_LIB_SPEC_SourceNative12, `PV_LIB_SPEC_StackRecheck12, `PV_LIB_SPEC_ThreadWords12, `PV_LIB_SPEC_NativeMemory12, `PV_LIB_SPEC_ThreadWordRecheck12, `PV_LIB_SPEC_AtomicRecheck12, `PV_LIB_SPEC_MemoryHistory12],
     #[`PV_LIB_SPEC_NativeKinds.atomicBool, `PV_LIB_SPEC_NativeKinds.unsafeCell, `PV_LIB_SPEC_NativeKinds.maybeDangling, `PV_LIB_SPEC_NativeKinds.boolCell, `PV_LIB_SPEC_AtomicBoolGap.zero, `PV_LIB_SPEC_AtomicBoolGap.numeric_rejected, `PV_LIB_SPEC_AtomicBoolGap.image_rejected, `PV_LIB_SPEC_NativeBoolArc.SiteType, `PV_LIB_SPEC_NativeBoolArc.classify, `PV_LIB_SPEC_NativeBoolArc.shape, `PV_LIB_SPEC_NativeBoolArc.threadWord, `PV_LIB_SPEC_NativeBoolArc.thread_word, `PV_LIB_SPEC_NativeBoolArc.scopeWord, `PV_LIB_SPEC_NativeBoolArc.image, `PV_LIB_SPEC_NativeBoolArc.reply, `PV_LIB_SPEC_NativeBoolArc.handler, `PV_LIB_SPEC_NativeBoolArc.returned_owned, `PV_LIB_SPEC_NativeBoolArc.scope_classified, `PV_LIB_SPEC_NativeBoolArc.packet_classified, `PV_LIB_SPEC_NativeBoolArc.layout_distinct, `PV_LIB_SPEC_NativeBoolArc.scope_image_word, `PV_LIB_SPEC_NativeBoolArc.scope_image_u8, `PV_LIB_SPEC_NativeConstructors.boolCell, `PV_LIB_SPEC_NativeConstructors.atomicBool, `PV_LIB_SPEC_NativeConstructors.value, `PV_LIB_SPEC_NativeConstructors.selected, `PV_LIB_SPEC_NativeConstructors.reply, `PV_LIB_SPEC_NativeConstructors.returned, `PV_LIB_SPEC_NativeConstructors.other, `PV_LIB_SPEC_NativeConstructors.framed, `PV_LIB_SPEC_NativeConstructors.initial_scope, `PV_LIB_SPEC_ThreadNewNative.operands, `PV_LIB_SPEC_ThreadNewNative.shape, `PV_LIB_SPEC_ThreadNewNative.rawReply, `PV_LIB_SPEC_ThreadNewNative.reply, `PV_LIB_SPEC_ThreadNewNative.ghost_frame, `PV_LIB_SPEC_NativeBoolRuntime.native, `PV_LIB_SPEC_NativeBoolRuntime.invalidPure, `PV_LIB_SPEC_NativeBoolRuntime.valueAnswer, `PV_LIB_SPEC_NativeBoolRuntime.answer, `PV_LIB_SPEC_NativeBoolRuntime.handler, `PV_LIB_SPEC_NativeBoolRuntime.ordinary_framed, `PV_LIB_SPEC_SuccessSchedule12.pointer, `PV_LIB_SPEC_SuccessSchedule12.allocation, `PV_LIB_SPEC_SuccessSchedule12.native, `PV_LIB_SPEC_SuccessSchedule12.environment, `PV_LIB_SPEC_SuccessSchedule12.parameters, `PV_LIB_SPEC_SuccessSchedule12.replies, `PV_LIB_SPEC_SuccessSchedule12.allocation_reply, `PV_LIB_SPEC_SuccessSchedule12.entry, `PV_LIB_SPEC_NativeBindings12.isArc, `PV_LIB_SPEC_NativeBindings12.core, `PV_LIB_SPEC_NativeBindings12.answer, `PV_LIB_SPEC_NativeBindings12.handler, `PV_LIB_SPEC_NativeBindings12.ordinary_framed, `PV_LIB_SPEC_NativeBindings12.transition, `PV_LIB_SPEC_NativeBindings12.control, `PV_LIB_SPEC_NativeBindings12.step, `PV_LIB_SPEC_NativeBindings12.run, `PV_LIB_SPEC_NativeBindings12.actions, `PV_LIB_SPEC_NativeBindings12.preserves_owner_away, `PV_LIB_SPEC_ThreadNewRecheck12.success, `PV_LIB_SPEC_ThreadNewRecheck12.sparse_stores, `PV_LIB_SPEC_NativeRecheck12.scope_handler, `PV_LIB_SPEC_NativeRecheck12.packet_reply, `PV_LIB_SPEC_NativeRecheck12.boolFn, `PV_LIB_SPEC_NativeRecheck12.cellFn, `PV_LIB_SPEC_NativeRecheck12.danglingFn, `PV_LIB_SPEC_NativeRecheck12.bool_value, `PV_LIB_SPEC_NativeRecheck12.cell_value, `PV_LIB_SPEC_NativeRecheck12.dangling_value, `PV_LIB_SPEC_NativeRecheck12.capture_constructor, `PV_LIB_SPEC_StackReferenceGap12.address, `PV_LIB_SPEC_StackReferenceGap12.reference, `PV_LIB_SPEC_StackReferenceGap12.store, `PV_LIB_SPEC_StackReferenceGap12.before, `PV_LIB_SPEC_StackReferenceGap12.C, `PV_LIB_SPEC_StackReferenceGap12.initialized, `PV_LIB_SPEC_StackReferenceGap12.unregistered, `PV_LIB_SPEC_StackReferenceGap12.physical_missing, `PV_LIB_SPEC_StackReferenceGap12.capture_missing, `PV_LIB_SPEC_PhysicalStack12.Frame, `PV_LIB_SPEC_PhysicalStack12.physical, `PV_LIB_SPEC_PhysicalStack12.captureWords, `PV_LIB_SPEC_PhysicalStack12.registers, `PV_LIB_SPEC_PhysicalStack12.defaultHooks, `PV_LIB_SPEC_PhysicalStack12.installDefault, `PV_LIB_SPEC_PhysicalStack12.default_mask, `PV_LIB_SPEC_PhysicalStack12.localFrame, `PV_LIB_SPEC_PhysicalStack12.localConfig, `PV_LIB_SPEC_PhysicalStack12.local_resolved, `PV_LIB_SPEC_PhysicalStack12.local_capture, `PV_LIB_SPEC_PhysicalStack12.default_snapshot, `PV_LIB_SPEC_PhysicalStack12.copies_default, `PV_LIB_SPEC_PhysicalStack12.stack_ghost, `PV_LIB_SPEC_StackCallback12.operands, `PV_LIB_SPEC_StackCallback12.native, `PV_LIB_SPEC_StackCallback12.operands_graph, `PV_LIB_SPEC_StackCallback12.at_call, `PV_LIB_SPEC_StackCallback12.missing_operands, `PV_LIB_SPEC_StackCallback12.answer, `PV_LIB_SPEC_StackCallback12.ordinary_framed, `PV_LIB_SPEC_SourceNative12.core, `PV_LIB_SPEC_SourceNative12.answer, `PV_LIB_SPEC_SourceNative12.handler, `PV_LIB_SPEC_SourceNative12.ordinary_framed, `PV_LIB_SPEC_SourceNative12.transition, `PV_LIB_SPEC_SourceNative12.control, `PV_LIB_SPEC_SourceNative12.step, `PV_LIB_SPEC_SourceNative12.run, `PV_LIB_SPEC_SourceNative12.actions, `PV_LIB_SPEC_SourceNative12.preserves_owner_away, `PV_LIB_SPEC_StackRecheck12.wrapped, `PV_LIB_SPEC_StackRecheck12.packet, `PV_LIB_SPEC_StackRecheck12.before, `PV_LIB_SPEC_StackRecheck12.source_reference, `PV_LIB_SPEC_StackRecheck12.operands, `PV_LIB_SPEC_StackRecheck12.callback, `PV_LIB_SPEC_ThreadWords12.Pointer, `PV_LIB_SPEC_ThreadWords12.read, `PV_LIB_SPEC_ThreadWords12.wordImage, `PV_LIB_SPEC_ThreadWords12.write, `PV_LIB_SPEC_ThreadWords12.read_written, `PV_LIB_SPEC_ThreadWords12.increment, `PV_LIB_SPEC_ThreadWords12.current, `PV_LIB_SPEC_ThreadWords12.clone, `PV_LIB_SPEC_ThreadWords12.current_other, `PV_LIB_SPEC_ThreadWords12.ghost_write, `PV_LIB_SPEC_NativeMemory12.Cut, `PV_LIB_SPEC_NativeMemory12.core, `PV_LIB_SPEC_NativeMemory12.answer, `PV_LIB_SPEC_NativeMemory12.handler, `PV_LIB_SPEC_NativeMemory12.ordinary_framed, `PV_LIB_SPEC_NativeMemory12.transition, `PV_LIB_SPEC_NativeMemory12.control, `PV_LIB_SPEC_NativeMemory12.step, `PV_LIB_SPEC_NativeMemory12.run, `PV_LIB_SPEC_NativeMemory12.actions, `PV_LIB_SPEC_NativeMemory12.preserves_owner_away, `PV_LIB_SPEC_ThreadWordRecheck12.read_away, `PV_LIB_SPEC_ThreadWordRecheck12.one, `PV_LIB_SPEC_ThreadWordRecheck12.inner, `PV_LIB_SPEC_ThreadWordRecheck12.prepared, `PV_LIB_SPEC_ThreadWordRecheck12.tls_word, `PV_LIB_SPEC_ThreadWordRecheck12.count_word, `PV_LIB_SPEC_ThreadWordRecheck12.current_success, `PV_LIB_SPEC_ThreadWordRecheck12.increment_written, `PV_LIB_SPEC_ThreadWordRecheck12.returned_thread_shape, `PV_LIB_SPEC_AtomicRecheck12.C, `PV_LIB_SPEC_AtomicRecheck12.before, `PV_LIB_SPEC_AtomicRecheck12.store, `PV_LIB_SPEC_AtomicRecheck12.loadFn, `PV_LIB_SPEC_AtomicRecheck12.entry, `PV_LIB_SPEC_AtomicRecheck12.load_constructor, `PV_LIB_SPEC_AtomicRecheck12.shared_zero, `PV_LIB_SPEC_MemoryHistory12.step, `PV_LIB_SPEC_MemoryHistory12.initial, `PV_LIB_SPEC_MemoryHistory12.run, `PV_LIB_SPEC_MemoryHistory12.original])
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
