import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_BoundNative13, `PV_LIB_SPEC_BoundRuntime, `PV_LIB_SPEC_Boundary, `PV_LIB_SPEC_Builder269, `PV_LIB_SPEC_CallbackBound, `PV_LIB_SPEC_CallbackCutCheck, `PV_LIB_SPEC_CallbackHistory, `PV_LIB_SPEC_CallbackImageGap, `PV_LIB_SPEC_CallbackModel, `PV_LIB_SPEC_CallbackModelHistory, `PV_LIB_SPEC_CallbackNativeGap, `PV_LIB_SPEC_CallbackOperands, `PV_LIB_SPEC_CallbackRecheck, `PV_LIB_SPEC_CallbackRuntime, `PV_LIB_SPEC_CallbackSource, `PV_LIB_SPEC_CallbackStores]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_BoundNative13.Cut, `PV_LIB_SPEC_BoundNative13.actions, `PV_LIB_SPEC_BoundNative13.answer, `PV_LIB_SPEC_BoundNative13.control, `PV_LIB_SPEC_BoundNative13.core, `PV_LIB_SPEC_BoundNative13.handler, `PV_LIB_SPEC_BoundNative13.ordinary_framed, `PV_LIB_SPEC_BoundNative13.preserves_owner_away, `PV_LIB_SPEC_BoundNative13.run, `PV_LIB_SPEC_BoundNative13.step, `PV_LIB_SPEC_BoundNative13.transition, `PV_LIB_SPEC_BoundRuntime.Machine, `PV_LIB_SPEC_BoundRuntime.MachineSpec, `PV_LIB_SPEC_BoundRuntime.allocationToken, `PV_LIB_SPEC_BoundRuntime.answer, `PV_LIB_SPEC_BoundRuntime.arc, `PV_LIB_SPEC_BoundRuntime.execute, `PV_LIB_SPEC_BoundRuntime.frameReply, `PV_LIB_SPEC_BoundRuntime.handler, `PV_LIB_SPEC_BoundRuntime.ordinary_framed, `PV_LIB_SPEC_BoundRuntime.run, `PV_LIB_SPEC_BoundRuntime.source, `PV_LIB_SPEC_BoundRuntime.step, `PV_LIB_SPEC_Boundary.Boundary, `PV_LIB_SPEC_Boundary.ConsumedPending, `PV_LIB_SPEC_Boundary.Diverges, `PV_LIB_SPEC_Boundary.First, `PV_LIB_SPEC_Boundary.Machine, `PV_LIB_SPEC_Boundary.Numbered, `PV_LIB_SPEC_Boundary.OwnComplete, `PV_LIB_SPEC_Boundary.RepresentationGap, `PV_LIB_SPEC_Boundary.State, `PV_LIB_SPEC_Boundary.Terminal, `PV_LIB_SPEC_Boundary.abort_prefix, `PV_LIB_SPEC_Boundary.body_not_pending, `PV_LIB_SPEC_Boundary.first_unique, `PV_LIB_SPEC_Boundary.observe, `PV_LIB_SPEC_Boundary.run, `PV_LIB_SPEC_Boundary.step, `PV_LIB_SPEC_Builder269.absent, `PV_LIB_SPEC_Builder269.builderKind, `PV_LIB_SPEC_Builder269.fields, `PV_LIB_SPEC_Builder269.frame, `PV_LIB_SPEC_Builder269.nameKind, `PV_LIB_SPEC_Builder269.reply, `PV_LIB_SPEC_Builder269.sizeKind, `PV_LIB_SPEC_Builder269.value, `PV_LIB_SPEC_CallbackBound.answer, `PV_LIB_SPEC_CallbackBound.at_call, `PV_LIB_SPEC_CallbackBound.missing_operands, `PV_LIB_SPEC_CallbackBound.native, `PV_LIB_SPEC_CallbackBound.operands, `PV_LIB_SPEC_CallbackBound.operands_graph, `PV_LIB_SPEC_CallbackBound.ordinary_framed, `PV_LIB_SPEC_CallbackCutCheck.actual_allocation, `PV_LIB_SPEC_CallbackCutCheck.actual_site, `PV_LIB_SPEC_CallbackCutCheck.backing_after_return, `PV_LIB_SPEC_CallbackCutCheck.different_cuts, `PV_LIB_SPEC_CallbackCutCheck.firstSite, `PV_LIB_SPEC_CallbackCutCheck.retained_cut, `PV_LIB_SPEC_CallbackCutCheck.retained_site, `PV_LIB_SPEC_CallbackHistory.initial, `PV_LIB_SPEC_CallbackHistory.original, `PV_LIB_SPEC_CallbackHistory.run]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_CallbackHistory.step, `PV_LIB_SPEC_CallbackImageGap.allocation_memory, `PV_LIB_SPEC_CallbackImageGap.binary_memory, `PV_LIB_SPEC_CallbackImageGap.memory_disagrees, `PV_LIB_SPEC_CallbackImageGap.unknown_copy, `PV_LIB_SPEC_CallbackModel.actions, `PV_LIB_SPEC_CallbackModel.answer, `PV_LIB_SPEC_CallbackModel.control, `PV_LIB_SPEC_CallbackModel.handler, `PV_LIB_SPEC_CallbackModel.isCallback, `PV_LIB_SPEC_CallbackModel.ordinary_framed, `PV_LIB_SPEC_CallbackModel.preserves_owner_away, `PV_LIB_SPEC_CallbackModel.run, `PV_LIB_SPEC_CallbackModel.step, `PV_LIB_SPEC_CallbackModel.transition, `PV_LIB_SPEC_CallbackModelHistory.initial, `PV_LIB_SPEC_CallbackModelHistory.original, `PV_LIB_SPEC_CallbackModelHistory.run, `PV_LIB_SPEC_CallbackModelHistory.step, `PV_LIB_SPEC_CallbackNativeGap.arc_away, `PV_LIB_SPEC_CallbackNativeGap.config, `PV_LIB_SPEC_CallbackNativeGap.distinct, `PV_LIB_SPEC_CallbackNativeGap.kind, `PV_LIB_SPEC_CallbackNativeGap.native, `PV_LIB_SPEC_CallbackNativeGap.native_disagrees, `PV_LIB_SPEC_CallbackNativeGap.native_memory, `PV_LIB_SPEC_CallbackNativeGap.parameters, `PV_LIB_SPEC_CallbackNativeGap.payload, `PV_LIB_SPEC_CallbackNativeGap.typeVariableArgument, `PV_LIB_SPEC_CallbackOperands.Registers, `PV_LIB_SPEC_CallbackOperands.captureWords, `PV_LIB_SPEC_CallbackOperands.capture_graph, `PV_LIB_SPEC_CallbackOperands.fromSource, `PV_LIB_SPEC_CallbackOperands.missing_run, `PV_LIB_SPEC_CallbackRecheck.backend, `PV_LIB_SPEC_CallbackRecheck.capture_length, `PV_LIB_SPEC_CallbackRecheck.capture_pointer, `PV_LIB_SPEC_CallbackRecheck.copied_unknown, `PV_LIB_SPEC_CallbackRecheck.ownership, `PV_LIB_SPEC_CallbackRuntime.answer, `PV_LIB_SPEC_CallbackRuntime.handler, `PV_LIB_SPEC_CallbackRuntime.invalidPure, `PV_LIB_SPEC_CallbackRuntime.native, `PV_LIB_SPEC_CallbackRuntime.native_at_call, `PV_LIB_SPEC_CallbackRuntime.native_memory, `PV_LIB_SPEC_CallbackRuntime.ordinary_framed, `PV_LIB_SPEC_CallbackRuntime.valueAnswer, `PV_LIB_SPEC_CallbackSource.Registers, `PV_LIB_SPEC_CallbackSource.at_call, `PV_LIB_SPEC_CallbackSource.native, `PV_LIB_SPEC_CallbackSource.other_answer, `PV_LIB_SPEC_CallbackSource.packet, `PV_LIB_SPEC_CallbackSource.packetWord, `PV_LIB_SPEC_CallbackSource.packet_capture, `PV_LIB_SPEC_CallbackSource.registers, `PV_LIB_SPEC_CallbackStores.Registers, `PV_LIB_SPEC_CallbackStores.at_call, `PV_LIB_SPEC_CallbackStores.copied, `PV_LIB_SPEC_CallbackStores.framed, `PV_LIB_SPEC_CallbackStores.handler, `PV_LIB_SPEC_CallbackStores.image]
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
