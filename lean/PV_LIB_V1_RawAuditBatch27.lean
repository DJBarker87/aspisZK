import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_SiteArcRecheck, `PV_LIB_SPEC_SiteHistory, `PV_LIB_SPEC_SiteRuntime, `PV_LIB_SPEC_SiteV2Runtime, `PV_LIB_SPEC_Source7Entry, `PV_LIB_SPEC_SourceNative12, `PV_LIB_SPEC_SourceProjection15, `PV_LIB_SPEC_SourceTransport15, `PV_LIB_SPEC_SparseArc, `PV_LIB_SPEC_SparseHistory, `PV_LIB_SPEC_SparsePacketHandler, `PV_LIB_SPEC_SparseRuntime, `PV_LIB_SPEC_SpawnHooks14, `PV_LIB_SPEC_StackCallback12, `PV_LIB_SPEC_StackRecheck12, `PV_LIB_SPEC_StackReferenceGap12]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_SiteArcRecheck.scope_image, `PV_LIB_SPEC_SiteHistory.initial, `PV_LIB_SPEC_SiteHistory.original, `PV_LIB_SPEC_SiteHistory.run, `PV_LIB_SPEC_SiteHistory.step, `PV_LIB_SPEC_SiteRuntime.answer, `PV_LIB_SPEC_SiteRuntime.handler, `PV_LIB_SPEC_SiteRuntime.invalidPure, `PV_LIB_SPEC_SiteRuntime.native, `PV_LIB_SPEC_SiteRuntime.ordinary_framed, `PV_LIB_SPEC_SiteRuntime.valueAnswer, `PV_LIB_SPEC_SiteV2Runtime.actions, `PV_LIB_SPEC_SiteV2Runtime.control, `PV_LIB_SPEC_SiteV2Runtime.preserves_owner_away, `PV_LIB_SPEC_SiteV2Runtime.run, `PV_LIB_SPEC_SiteV2Runtime.step, `PV_LIB_SPEC_SiteV2Runtime.transition, `PV_LIB_SPEC_Source7Entry.aligned, `PV_LIB_SPEC_Source7Entry.chosen_header, `PV_LIB_SPEC_Source7Entry.column, `PV_LIB_SPEC_Source7Entry.entry_nonempty, `PV_LIB_SPEC_Source7Entry.foundation, `PV_LIB_SPEC_Source7Entry.header, `PV_LIB_SPEC_Source7Entry.identities, `PV_LIB_SPEC_Source7Entry.identity_zero, `PV_LIB_SPEC_Source7Entry.indexed, `PV_LIB_SPEC_Source7Entry.owned, `PV_LIB_SPEC_Source7Entry.owner_wellFormed, `PV_LIB_SPEC_Source7Entry.receiver_source, `PV_LIB_SPEC_Source7Entry.shape, `PV_LIB_SPEC_Source7Entry.source, `PV_LIB_SPEC_Source7Entry.state, `PV_LIB_SPEC_Source7Entry.store, `PV_LIB_SPEC_Source7Entry.toVecEntry, `PV_LIB_SPEC_Source7Entry.toVec_entry_nonempty, `PV_LIB_SPEC_Source7Entry.toVec_pre, `PV_LIB_SPEC_Source7Entry.typed_source, `PV_LIB_SPEC_Source7Entry.valid, `PV_LIB_SPEC_Source7Entry.values_empty, `PV_LIB_SPEC_SourceNative12.actions, `PV_LIB_SPEC_SourceNative12.answer, `PV_LIB_SPEC_SourceNative12.control, `PV_LIB_SPEC_SourceNative12.core, `PV_LIB_SPEC_SourceNative12.handler, `PV_LIB_SPEC_SourceNative12.ordinary_framed, `PV_LIB_SPEC_SourceNative12.preserves_owner_away, `PV_LIB_SPEC_SourceNative12.run, `PV_LIB_SPEC_SourceNative12.step, `PV_LIB_SPEC_SourceNative12.transition, `PV_LIB_SPEC_SourceProjection15.no_wait, `PV_LIB_SPEC_SourceProjection15.state, `PV_LIB_SPEC_SourceProjection15.transport, `PV_LIB_SPEC_SourceTransport15.Quiet, `PV_LIB_SPEC_SourceTransport15.Trace, `PV_LIB_SPEC_SourceTransport15.advance, `PV_LIB_SPEC_SourceTransport15.run, `PV_LIB_SPEC_SourceTransport15.sourceStep, `PV_LIB_SPEC_SourceTransport15.transition, `PV_LIB_SPEC_SparseArc.binary_agreement, `PV_LIB_SPEC_SparseArc.descriptor, `PV_LIB_SPEC_SparseArc.image, `PV_LIB_SPEC_SparseArc.initialized, `PV_LIB_SPEC_SparseArc.memory, `PV_LIB_SPEC_SparseArc.other]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_SparseArc.owned, `PV_LIB_SPEC_SparseArc.payload, `PV_LIB_SPEC_SparseArc.reply, `PV_LIB_SPEC_SparseArc.returned, `PV_LIB_SPEC_SparseArc.returned_owned, `PV_LIB_SPEC_SparseArc.shape, `PV_LIB_SPEC_SparseArc.unwritten, `PV_LIB_SPEC_SparseArc.written, `PV_LIB_SPEC_SparseHistory.initial, `PV_LIB_SPEC_SparseHistory.original, `PV_LIB_SPEC_SparseHistory.run, `PV_LIB_SPEC_SparseHistory.step, `PV_LIB_SPEC_SparsePacketHandler.at_call, `PV_LIB_SPEC_SparsePacketHandler.away, `PV_LIB_SPEC_SparsePacketHandler.decode, `PV_LIB_SPEC_SparsePacketHandler.handler, `PV_LIB_SPEC_SparsePacketHandler.physical, `PV_LIB_SPEC_SparsePacketHandler.scopeWord, `PV_LIB_SPEC_SparseRuntime.answer, `PV_LIB_SPEC_SparseRuntime.controlStep, `PV_LIB_SPEC_SparseRuntime.handler, `PV_LIB_SPEC_SparseRuntime.invalidPure, `PV_LIB_SPEC_SparseRuntime.machineAt, `PV_LIB_SPEC_SparseRuntime.native, `PV_LIB_SPEC_SparseRuntime.ordinary_framed, `PV_LIB_SPEC_SparseRuntime.pureValue, `PV_LIB_SPEC_SparseRuntime.run, `PV_LIB_SPEC_SparseRuntime.step, `PV_LIB_SPEC_SparseRuntime.valueAnswer, `PV_LIB_SPEC_SparseRuntime.values, `PV_LIB_SPEC_SpawnHooks14.defaultReply, `PV_LIB_SPEC_SpawnHooks14.empty, `PV_LIB_SPEC_SpawnHooks14.empty_initialized, `PV_LIB_SPEC_SpawnHooks14.fields, `PV_LIB_SPEC_SpawnHooks14.hooks, `PV_LIB_SPEC_SpawnHooks14.other, `PV_LIB_SPEC_SpawnHooks14.output, `PV_LIB_SPEC_SpawnHooks14.raw, `PV_LIB_SPEC_SpawnHooks14.reply, `PV_LIB_SPEC_SpawnHooks14.result, `PV_LIB_SPEC_SpawnHooks14.thread, `PV_LIB_SPEC_SpawnHooks14.value, `PV_LIB_SPEC_StackCallback12.answer, `PV_LIB_SPEC_StackCallback12.at_call, `PV_LIB_SPEC_StackCallback12.missing_operands, `PV_LIB_SPEC_StackCallback12.native, `PV_LIB_SPEC_StackCallback12.operands, `PV_LIB_SPEC_StackCallback12.operands_graph, `PV_LIB_SPEC_StackCallback12.ordinary_framed, `PV_LIB_SPEC_StackRecheck12.before, `PV_LIB_SPEC_StackRecheck12.callback, `PV_LIB_SPEC_StackRecheck12.operands, `PV_LIB_SPEC_StackRecheck12.packet, `PV_LIB_SPEC_StackRecheck12.source_reference, `PV_LIB_SPEC_StackRecheck12.wrapped, `PV_LIB_SPEC_StackReferenceGap12.C, `PV_LIB_SPEC_StackReferenceGap12.address, `PV_LIB_SPEC_StackReferenceGap12.before, `PV_LIB_SPEC_StackReferenceGap12.capture_missing, `PV_LIB_SPEC_StackReferenceGap12.initialized, `PV_LIB_SPEC_StackReferenceGap12.physical_missing]
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
