import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_CallbackBound, `PV_LIB_SPEC_CallbackHistory, `PV_LIB_SPEC_CallbackModel, `PV_LIB_SPEC_CallbackModelHistory, `PV_LIB_SPEC_CallbackOperands, `PV_LIB_SPEC_CallbackRecheck, `PV_LIB_SPEC_CallbackRuntime, `PV_LIB_SPEC_CallbackSource, `PV_LIB_SPEC_CallbackStores, `PV_LIB_SPEC_CallbackV2Runtime, `PV_LIB_SPEC_NativeHistory, `PV_LIB_SPEC_NativeModel, `PV_LIB_SPEC_ThreadRepresentationGap, `PV_LIB_SPEC_WordThreadArc, `PV_LIB_SPEC_WordThreadRecheck, `PV_LIB_SPEC_WordThreadRuntime],
     #[`PV_LIB_SPEC_CallbackBound.operands, `PV_LIB_SPEC_CallbackBound.native, `PV_LIB_SPEC_CallbackBound.operands_graph, `PV_LIB_SPEC_CallbackBound.at_call, `PV_LIB_SPEC_CallbackBound.missing_operands, `PV_LIB_SPEC_CallbackBound.answer, `PV_LIB_SPEC_CallbackBound.ordinary_framed, `PV_LIB_SPEC_CallbackHistory.step, `PV_LIB_SPEC_CallbackHistory.initial, `PV_LIB_SPEC_CallbackHistory.run, `PV_LIB_SPEC_CallbackHistory.original, `PV_LIB_SPEC_CallbackModel.isCallback, `PV_LIB_SPEC_CallbackModel.answer, `PV_LIB_SPEC_CallbackModel.handler, `PV_LIB_SPEC_CallbackModel.ordinary_framed, `PV_LIB_SPEC_CallbackModel.transition, `PV_LIB_SPEC_CallbackModel.control, `PV_LIB_SPEC_CallbackModel.step, `PV_LIB_SPEC_CallbackModel.run, `PV_LIB_SPEC_CallbackModel.actions, `PV_LIB_SPEC_CallbackModel.preserves_owner_away, `PV_LIB_SPEC_CallbackModelHistory.step, `PV_LIB_SPEC_CallbackModelHistory.initial, `PV_LIB_SPEC_CallbackModelHistory.run, `PV_LIB_SPEC_CallbackModelHistory.original, `PV_LIB_SPEC_CallbackOperands.Registers, `PV_LIB_SPEC_CallbackOperands.captureWords, `PV_LIB_SPEC_CallbackOperands.fromSource, `PV_LIB_SPEC_CallbackOperands.capture_graph, `PV_LIB_SPEC_CallbackOperands.missing_run, `PV_LIB_SPEC_CallbackRecheck.ownership, `PV_LIB_SPEC_CallbackRecheck.capture_pointer, `PV_LIB_SPEC_CallbackRecheck.capture_length, `PV_LIB_SPEC_CallbackRecheck.backend, `PV_LIB_SPEC_CallbackRecheck.copied_unknown, `PV_LIB_SPEC_CallbackRuntime.native, `PV_LIB_SPEC_CallbackRuntime.invalidPure, `PV_LIB_SPEC_CallbackRuntime.valueAnswer, `PV_LIB_SPEC_CallbackRuntime.answer, `PV_LIB_SPEC_CallbackRuntime.handler, `PV_LIB_SPEC_CallbackRuntime.ordinary_framed, `PV_LIB_SPEC_CallbackRuntime.native_at_call, `PV_LIB_SPEC_CallbackRuntime.native_memory, `PV_LIB_SPEC_CallbackSource.Registers, `PV_LIB_SPEC_CallbackSource.packetWord, `PV_LIB_SPEC_CallbackSource.packet, `PV_LIB_SPEC_CallbackSource.registers, `PV_LIB_SPEC_CallbackSource.native, `PV_LIB_SPEC_CallbackSource.packet_capture, `PV_LIB_SPEC_CallbackSource.at_call, `PV_LIB_SPEC_CallbackSource.other_answer, `PV_LIB_SPEC_CallbackStores.Registers, `PV_LIB_SPEC_CallbackStores.image, `PV_LIB_SPEC_CallbackStores.reply, `PV_LIB_SPEC_CallbackStores.handler, `PV_LIB_SPEC_CallbackStores.resource_answer, `PV_LIB_SPEC_CallbackStores.at_call, `PV_LIB_SPEC_CallbackStores.success, `PV_LIB_SPEC_CallbackStores.framed, `PV_LIB_SPEC_CallbackStores.copied, `PV_LIB_SPEC_CallbackStores.packet_word, `PV_LIB_SPEC_CallbackStores.tail, `PV_LIB_SPEC_CallbackV2Runtime.transition, `PV_LIB_SPEC_CallbackV2Runtime.control, `PV_LIB_SPEC_CallbackV2Runtime.step, `PV_LIB_SPEC_CallbackV2Runtime.run, `PV_LIB_SPEC_CallbackV2Runtime.actions, `PV_LIB_SPEC_CallbackV2Runtime.preserves_owner_away, `PV_LIB_SPEC_NativeHistory.step, `PV_LIB_SPEC_NativeHistory.initial, `PV_LIB_SPEC_NativeHistory.run, `PV_LIB_SPEC_NativeHistory.original, `PV_LIB_SPEC_NativeModel.isArc, `PV_LIB_SPEC_NativeModel.answer, `PV_LIB_SPEC_NativeModel.handler, `PV_LIB_SPEC_NativeModel.ordinary_framed, `PV_LIB_SPEC_NativeModel.callback, `PV_LIB_SPEC_NativeModel.transition, `PV_LIB_SPEC_NativeModel.control, `PV_LIB_SPEC_NativeModel.step, `PV_LIB_SPEC_NativeModel.run, `PV_LIB_SPEC_NativeModel.actions, `PV_LIB_SPEC_NativeModel.preserves_owner_away, `PV_LIB_SPEC_ThreadRepresentationGap.thread_word, `PV_LIB_SPEC_ThreadRepresentationGap.shaped_thread, `PV_LIB_SPEC_ThreadRepresentationGap.scope_handler, `PV_LIB_SPEC_ThreadRepresentationGap.incompatible, `PV_LIB_SPEC_WordThreadArc.SiteType, `PV_LIB_SPEC_WordThreadArc.classify, `PV_LIB_SPEC_WordThreadArc.shape, `PV_LIB_SPEC_WordThreadArc.threadWord, `PV_LIB_SPEC_WordThreadArc.thread_word, `PV_LIB_SPEC_WordThreadArc.scopeWord, `PV_LIB_SPEC_WordThreadArc.image, `PV_LIB_SPEC_WordThreadArc.reply, `PV_LIB_SPEC_WordThreadArc.handler, `PV_LIB_SPEC_WordThreadArc.returned_owned, `PV_LIB_SPEC_WordThreadArc.scope_classified, `PV_LIB_SPEC_WordThreadArc.packet_classified, `PV_LIB_SPEC_WordThreadArc.layout_distinct, `PV_LIB_SPEC_WordThreadArc.scope_image_word, `PV_LIB_SPEC_WordThreadRecheck.scope_handler, `PV_LIB_SPEC_WordThreadRecheck.packet_reply, `PV_LIB_SPEC_WordThreadRecheck.thread_shape, `PV_LIB_SPEC_WordThreadRuntime.native, `PV_LIB_SPEC_WordThreadRuntime.invalidPure, `PV_LIB_SPEC_WordThreadRuntime.valueAnswer, `PV_LIB_SPEC_WordThreadRuntime.answer, `PV_LIB_SPEC_WordThreadRuntime.handler, `PV_LIB_SPEC_WordThreadRuntime.ordinary_framed])
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
