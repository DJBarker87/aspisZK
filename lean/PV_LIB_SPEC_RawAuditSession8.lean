import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_SparseArc, `PV_LIB_SPEC_SparsePacketHandler, `PV_LIB_SPEC_SparseRuntime, `PV_LIB_SPEC_CallbackCutCheck, `PV_LIB_SPEC_SparseHistory, `PV_LIB_SPEC_SuccessResources, `PV_LIB_SPEC_LocalOwnership, `PV_LIB_SPEC_LocalInitMemory],
     #[`PV_LIB_SPEC_SparseArc.shape, `PV_LIB_SPEC_SparseArc.image, `PV_LIB_SPEC_SparseArc.memory, `PV_LIB_SPEC_SparseArc.initialized, `PV_LIB_SPEC_SparseArc.binary_agreement, `PV_LIB_SPEC_SparseArc.written, `PV_LIB_SPEC_SparseArc.unwritten, `PV_LIB_SPEC_SparseArc.payload, `PV_LIB_SPEC_SparseArc.descriptor, `PV_LIB_SPEC_SparseArc.owned, `PV_LIB_SPEC_SparseArc.reply, `PV_LIB_SPEC_SparseArc.returned, `PV_LIB_SPEC_SparseArc.returned_owned, `PV_LIB_SPEC_SparseArc.other, `PV_LIB_SPEC_SparsePacketHandler.physical, `PV_LIB_SPEC_SparsePacketHandler.scopeWord, `PV_LIB_SPEC_SparsePacketHandler.decode, `PV_LIB_SPEC_SparsePacketHandler.handler, `PV_LIB_SPEC_SparsePacketHandler.away, `PV_LIB_SPEC_SparsePacketHandler.at_call, `PV_LIB_SPEC_SparseRuntime.pureValue, `PV_LIB_SPEC_SparseRuntime.values, `PV_LIB_SPEC_SparseRuntime.native, `PV_LIB_SPEC_SparseRuntime.invalidPure, `PV_LIB_SPEC_SparseRuntime.valueAnswer, `PV_LIB_SPEC_SparseRuntime.answer, `PV_LIB_SPEC_SparseRuntime.handler, `PV_LIB_SPEC_SparseRuntime.machineAt, `PV_LIB_SPEC_SparseRuntime.controlStep, `PV_LIB_SPEC_SparseRuntime.step, `PV_LIB_SPEC_SparseRuntime.run, `PV_LIB_SPEC_SparseRuntime.ordinary_framed, `PV_LIB_SPEC_CallbackCutCheck.backing_after_return, `PV_LIB_SPEC_CallbackCutCheck.actual_allocation, `PV_LIB_SPEC_CallbackCutCheck.retained_cut, `PV_LIB_SPEC_CallbackCutCheck.firstSite, `PV_LIB_SPEC_CallbackCutCheck.actual_site, `PV_LIB_SPEC_CallbackCutCheck.retained_site, `PV_LIB_SPEC_CallbackCutCheck.different_cuts, `PV_LIB_SPEC_SparseHistory.step, `PV_LIB_SPEC_SparseHistory.initial, `PV_LIB_SPEC_SparseHistory.run, `PV_LIB_SPEC_SparseHistory.original, `PV_LIB_SPEC_SuccessResources.allocation, `PV_LIB_SPEC_SuccessResources.initResources, `PV_LIB_SPEC_SuccessResources.callbackResources, `PV_LIB_SPEC_SuccessResources.packet, `PV_LIB_SPEC_SuccessResources.callback, `PV_LIB_SPEC_SuccessResources.init, `PV_LIB_SPEC_SuccessResources.local_init, `PV_LIB_SPEC_SuccessResources.local_callback, `PV_LIB_SPEC_LocalOwnership.allocationStore, `PV_LIB_SPEC_LocalOwnership.sourceStore, `PV_LIB_SPEC_LocalOwnership.encode, `PV_LIB_SPEC_LocalOwnership.before, `PV_LIB_SPEC_LocalOwnership.allocated, `PV_LIB_SPEC_LocalOwnership.registered, `PV_LIB_SPEC_LocalOwnership.pre, `PV_LIB_SPEC_LocalOwnership.handle, `PV_LIB_SPEC_LocalOwnership.data, `PV_LIB_SPEC_LocalOwnership.loadBias, `PV_LIB_SPEC_LocalOwnership.index, `PV_LIB_SPEC_LocalOwnership.payload, `PV_LIB_SPEC_LocalOwnership.readyStore, `PV_LIB_SPEC_LocalOwnership.ready, `PV_LIB_SPEC_LocalOwnership.q, `PV_LIB_SPEC_LocalOwnership.granted, `PV_LIB_SPEC_LocalOwnership.metadata, `PV_LIB_SPEC_LocalOwnership.old_range, `PV_LIB_SPEC_LocalOwnership.fresh, `PV_LIB_SPEC_LocalOwnership.C, `PV_LIB_SPEC_LocalOwnership.K, `PV_LIB_SPEC_LocalOwnership.P, `PV_LIB_SPEC_LocalOwnership.H, `PV_LIB_SPEC_LocalOwnership.words, `PV_LIB_SPEC_LocalOwnership.allocationReply, `PV_LIB_SPEC_LocalOwnership.post, `PV_LIB_SPEC_LocalOwnership.applied, `PV_LIB_SPEC_LocalOwnership.ownership_export, `PV_LIB_SPEC_LocalInitMemory.successful, `PV_LIB_SPEC_LocalInitMemory.no_callback_destination])
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
