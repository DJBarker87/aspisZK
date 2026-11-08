import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_AllocationImages, `PV_LIB_SPEC_AllocationSites, `PV_LIB_SPEC_SiteArc, `PV_LIB_SPEC_InitImageRecheck, `PV_LIB_SPEC_SiteRuntime, `PV_LIB_SPEC_SiteArcRecheck, `PV_LIB_SPEC_SiteV2Runtime, `PV_LIB_SPEC_SiteHistory, `PV_LIB_SPEC_CallbackImageGap, `PV_LIB_SPEC_CallbackNativeGap],
     #[`PV_LIB_SPEC_AllocationImages.Image, `PV_LIB_SPEC_AllocationImages.Memory, `PV_LIB_SPEC_AllocationImages.byte, `PV_LIB_SPEC_AllocationImages.word, `PV_LIB_SPEC_AllocationImages.scope, `PV_LIB_SPEC_AllocationImages.packet, `PV_LIB_SPEC_AllocationImages.callback, `PV_LIB_SPEC_AllocationImages.threadInit, `PV_LIB_SPEC_AllocationImages.threadInner, `PV_LIB_SPEC_AllocationImages.overwrite, `PV_LIB_SPEC_AllocationImages.initialized, `PV_LIB_SPEC_AllocationImages.stored, `PV_LIB_SPEC_AllocationImages.hole, `PV_LIB_SPEC_AllocationImages.scope_hole, `PV_LIB_SPEC_AllocationImages.packet_hole, `PV_LIB_SPEC_AllocationImages.callback_copy, `PV_LIB_SPEC_AllocationImages.callback_hole, `PV_LIB_SPEC_AllocationImages.init_hole, `PV_LIB_SPEC_AllocationImages.thread_hole, `PV_LIB_SPEC_AllocationImages.packet_agreement, `PV_LIB_SPEC_AllocationImages.ghost, `PV_LIB_SPEC_AllocationImages.receiver_frame, `PV_LIB_SPEC_AllocationImages.owned_frame, `PV_LIB_SPEC_AllocationSites.Site, `PV_LIB_SPEC_AllocationSites.CopyOperands, `PV_LIB_SPEC_AllocationSites.Operands, `PV_LIB_SPEC_AllocationSites.width, `PV_LIB_SPEC_AllocationSites.alignment, `PV_LIB_SPEC_AllocationSites.writtenLength, `PV_LIB_SPEC_AllocationSites.image, `PV_LIB_SPEC_AllocationSites.scope_mask, `PV_LIB_SPEC_AllocationSites.packet_mask, `PV_LIB_SPEC_AllocationSites.callback_mask, `PV_LIB_SPEC_AllocationSites.init_mask, `PV_LIB_SPEC_AllocationSites.thread_mask, `PV_LIB_SPEC_AllocationSites.mask, `PV_LIB_SPEC_AllocationSites.stores_within_layout, `PV_LIB_SPEC_AllocationSites.retains_tail, `PV_LIB_SPEC_SiteArc.SiteType, `PV_LIB_SPEC_SiteArc.classify, `PV_LIB_SPEC_SiteArc.shape, `PV_LIB_SPEC_SiteArc.threadWord, `PV_LIB_SPEC_SiteArc.scopeWord, `PV_LIB_SPEC_SiteArc.image, `PV_LIB_SPEC_SiteArc.reply, `PV_LIB_SPEC_SiteArc.handler, `PV_LIB_SPEC_SiteArc.returned_owned, `PV_LIB_SPEC_SiteArc.scope_classified, `PV_LIB_SPEC_SiteArc.packet_classified, `PV_LIB_SPEC_SiteArc.layout_distinct, `PV_LIB_SPEC_InitImageRecheck.first, `PV_LIB_SPEC_InitImageRecheck.second, `PV_LIB_SPEC_InitImageRecheck.third, `PV_LIB_SPEC_InitImageRecheck.memory_agreement, `PV_LIB_SPEC_InitImageRecheck.initPost_memory, `PV_LIB_SPEC_SiteRuntime.native, `PV_LIB_SPEC_SiteRuntime.invalidPure, `PV_LIB_SPEC_SiteRuntime.valueAnswer, `PV_LIB_SPEC_SiteRuntime.answer, `PV_LIB_SPEC_SiteRuntime.handler, `PV_LIB_SPEC_SiteRuntime.ordinary_framed, `PV_LIB_SPEC_SiteArcRecheck.panic, `PV_LIB_SPEC_SiteArcRecheck.scope_image, `PV_LIB_SPEC_SiteArcRecheck.scope_handler, `PV_LIB_SPEC_SiteArcRecheck.packet_reply, `PV_LIB_SPEC_SiteV2Runtime.transition, `PV_LIB_SPEC_SiteV2Runtime.control, `PV_LIB_SPEC_SiteV2Runtime.step, `PV_LIB_SPEC_SiteV2Runtime.run, `PV_LIB_SPEC_SiteV2Runtime.actions, `PV_LIB_SPEC_SiteV2Runtime.preserves_owner_away, `PV_LIB_SPEC_SiteHistory.step, `PV_LIB_SPEC_SiteHistory.initial, `PV_LIB_SPEC_SiteHistory.run, `PV_LIB_SPEC_SiteHistory.original, `PV_LIB_SPEC_CallbackImageGap.allocation_memory, `PV_LIB_SPEC_CallbackImageGap.binary_memory, `PV_LIB_SPEC_CallbackImageGap.memory_disagrees, `PV_LIB_SPEC_CallbackImageGap.unknown_copy, `PV_LIB_SPEC_CallbackNativeGap.kind, `PV_LIB_SPEC_CallbackNativeGap.payload, `PV_LIB_SPEC_CallbackNativeGap.typeVariableArgument, `PV_LIB_SPEC_CallbackNativeGap.distinct, `PV_LIB_SPEC_CallbackNativeGap.arc_away, `PV_LIB_SPEC_CallbackNativeGap.native, `PV_LIB_SPEC_CallbackNativeGap.parameters, `PV_LIB_SPEC_CallbackNativeGap.config, `PV_LIB_SPEC_CallbackNativeGap.native_memory, `PV_LIB_SPEC_CallbackNativeGap.native_disagrees])
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
