import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_ActiveBoundary19, `PV_LIB_SPEC_ActiveConsumption19, `PV_LIB_SPEC_ActiveCorrection19, `PV_LIB_SPEC_ActiveNative19, `PV_LIB_SPEC_ActiveReplacement16, `PV_LIB_SPEC_ActiveSource19, `PV_LIB_SPEC_AllocationImages, `PV_LIB_SPEC_AllocationSites, `PV_LIB_SPEC_ArcImageGap, `PV_LIB_SPEC_ArcPhysical13, `PV_LIB_SPEC_ArcPhysicalGap13, `PV_LIB_SPEC_AssembledChecks14, `PV_LIB_SPEC_AssembledSize14, `PV_LIB_SPEC_Assembly14, `PV_LIB_SPEC_AssemblyEnvironment14, `PV_LIB_SPEC_AtomicBindings13, `PV_LIB_SPEC_AtomicBoolGap, `PV_LIB_SPEC_AtomicRecheck12, `PV_LIB_SPEC_BinaryStack16]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_ActiveBoundary19.successful, `PV_LIB_SPEC_ActiveConsumption19.bound, `PV_LIB_SPEC_ActiveConsumption19.consume, `PV_LIB_SPEC_ActiveConsumption19.delivered, `PV_LIB_SPEC_ActiveConsumption19.events, `PV_LIB_SPEC_ActiveConsumption19.physical, `PV_LIB_SPEC_ActiveCorrection19.after_status, `PV_LIB_SPEC_ActiveCorrection19.before, `PV_LIB_SPEC_ActiveCorrection19.nonstall, `PV_LIB_SPEC_ActiveNative19.answer, `PV_LIB_SPEC_ActiveNative19.different, `PV_LIB_SPEC_ActiveNative19.not_tls, `PV_LIB_SPEC_ActiveNative19.request, `PV_LIB_SPEC_ActiveNative19.token, `PV_LIB_SPEC_ActiveNative19.trigger, `PV_LIB_SPEC_ActiveReplacement16.physical, `PV_LIB_SPEC_ActiveReplacement16.source_write, `PV_LIB_SPEC_ActiveSource19.cell, `PV_LIB_SPEC_ActiveSource19.frame, `PV_LIB_SPEC_ActiveSource19.status, `PV_LIB_SPEC_ActiveSource19.store, `PV_LIB_SPEC_AllocationImages.Image, `PV_LIB_SPEC_AllocationImages.Memory, `PV_LIB_SPEC_AllocationImages.byte, `PV_LIB_SPEC_AllocationImages.callback, `PV_LIB_SPEC_AllocationImages.callback_copy, `PV_LIB_SPEC_AllocationImages.callback_hole, `PV_LIB_SPEC_AllocationImages.ghost, `PV_LIB_SPEC_AllocationImages.hole, `PV_LIB_SPEC_AllocationImages.init_hole, `PV_LIB_SPEC_AllocationImages.initialized, `PV_LIB_SPEC_AllocationImages.overwrite, `PV_LIB_SPEC_AllocationImages.owned_frame, `PV_LIB_SPEC_AllocationImages.packet, `PV_LIB_SPEC_AllocationImages.packet_agreement, `PV_LIB_SPEC_AllocationImages.packet_hole, `PV_LIB_SPEC_AllocationImages.receiver_frame, `PV_LIB_SPEC_AllocationImages.scope, `PV_LIB_SPEC_AllocationImages.scope_hole, `PV_LIB_SPEC_AllocationImages.stored, `PV_LIB_SPEC_AllocationImages.threadInit, `PV_LIB_SPEC_AllocationImages.threadInner, `PV_LIB_SPEC_AllocationImages.thread_hole, `PV_LIB_SPEC_AllocationImages.word, `PV_LIB_SPEC_AllocationSites.CopyOperands, `PV_LIB_SPEC_AllocationSites.Operands, `PV_LIB_SPEC_AllocationSites.Site, `PV_LIB_SPEC_AllocationSites.alignment, `PV_LIB_SPEC_AllocationSites.callback_mask, `PV_LIB_SPEC_AllocationSites.image, `PV_LIB_SPEC_AllocationSites.init_mask, `PV_LIB_SPEC_AllocationSites.mask, `PV_LIB_SPEC_AllocationSites.packet_mask, `PV_LIB_SPEC_AllocationSites.retains_tail, `PV_LIB_SPEC_AllocationSites.scope_mask, `PV_LIB_SPEC_AllocationSites.stores_within_layout, `PV_LIB_SPEC_AllocationSites.thread_mask, `PV_LIB_SPEC_AllocationSites.width, `PV_LIB_SPEC_AllocationSites.writtenLength, `PV_LIB_SPEC_ArcImageGap.alignment, `PV_LIB_SPEC_ArcImageGap.binaryInitialized, `PV_LIB_SPEC_ArcImageGap.binary_frames_payload, `PV_LIB_SPEC_ArcImageGap.byte, `PV_LIB_SPEC_ArcImageGap.dataOffset]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_ArcImageGap.dataWidth, `PV_LIB_SPEC_ArcImageGap.initialImage, `PV_LIB_SPEC_ArcImageGap.initializedMemory, `PV_LIB_SPEC_ArcImageGap.no_exact_total_image, `PV_LIB_SPEC_ArcImageGap.source_hole, `PV_LIB_SPEC_ArcImageGap.strongOffset, `PV_LIB_SPEC_ArcImageGap.total_image_disagrees, `PV_LIB_SPEC_ArcImageGap.weakOffset, `PV_LIB_SPEC_ArcImageGap.width, `PV_LIB_SPEC_ArcPhysical13.one_to_two, `PV_LIB_SPEC_ArcPhysical13.operands, `PV_LIB_SPEC_ArcPhysical13.reply, `PV_LIB_SPEC_ArcPhysical13.write_away, `PV_LIB_SPEC_ArcPhysicalGap13.byte_conflict, `PV_LIB_SPEC_ArcPhysicalGap13.drops_physical_write, `PV_LIB_SPEC_AssembledChecks14.cut, `PV_LIB_SPEC_AssembledChecks14.different, `PV_LIB_SPEC_AssembledChecks14.f454, `PV_LIB_SPEC_AssembledSize14.arguments, `PV_LIB_SPEC_AssembledSize14.different, `PV_LIB_SPEC_AssembledSize14.f295, `PV_LIB_SPEC_Assembly14.Cut, `PV_LIB_SPEC_Assembly14.actions, `PV_LIB_SPEC_Assembly14.answer, `PV_LIB_SPEC_Assembly14.control, `PV_LIB_SPEC_Assembly14.core, `PV_LIB_SPEC_Assembly14.handler, `PV_LIB_SPEC_Assembly14.ordinary_framed, `PV_LIB_SPEC_Assembly14.preserves_owner_away, `PV_LIB_SPEC_Assembly14.run, `PV_LIB_SPEC_Assembly14.step, `PV_LIB_SPEC_Assembly14.transition, `PV_LIB_SPEC_AssemblyEnvironment14.allocations, `PV_LIB_SPEC_AssemblyEnvironment14.environment, `PV_LIB_SPEC_AssemblyEnvironment14.native, `PV_LIB_SPEC_AssemblyEnvironment14.parameters, `PV_LIB_SPEC_AssemblyEnvironment14.pre, `PV_LIB_SPEC_AtomicBindings13.args, `PV_LIB_SPEC_AtomicBindings13.config, `PV_LIB_SPEC_AtomicBindings13.constructor_load, `PV_LIB_SPEC_AtomicBindings13.effects, `PV_LIB_SPEC_AtomicBindings13.entry, `PV_LIB_SPEC_AtomicBindings13.load, `PV_LIB_SPEC_AtomicBindings13.other, `PV_LIB_SPEC_AtomicBindings13.reply, `PV_LIB_SPEC_AtomicBoolGap.image_rejected, `PV_LIB_SPEC_AtomicBoolGap.numeric_rejected, `PV_LIB_SPEC_AtomicBoolGap.zero, `PV_LIB_SPEC_AtomicRecheck12.C, `PV_LIB_SPEC_AtomicRecheck12.before, `PV_LIB_SPEC_AtomicRecheck12.entry, `PV_LIB_SPEC_AtomicRecheck12.loadFn, `PV_LIB_SPEC_AtomicRecheck12.load_constructor, `PV_LIB_SPEC_AtomicRecheck12.shared_zero, `PV_LIB_SPEC_AtomicRecheck12.store, `PV_LIB_SPEC_BinaryStack16.argument_slots, `PV_LIB_SPEC_BinaryStack16.coordinates, `PV_LIB_SPEC_BinaryStack16.frame, `PV_LIB_SPEC_BinaryStack16.prologues, `PV_LIB_SPEC_BinaryStack16.scopeRsp, `PV_LIB_SPEC_BinaryStack16.spawnRsp]
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
