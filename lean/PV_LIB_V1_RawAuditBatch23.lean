import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_InitializedWords13, `PV_LIB_SPEC_JointPremises, `PV_LIB_SPEC_LaneAJoins16, `PV_LIB_SPEC_LaneAJoins18, `PV_LIB_SPEC_LaneAJoins19, `PV_LIB_SPEC_LaneAStoreInput, `PV_LIB_SPEC_LocalInitMemory, `PV_LIB_SPEC_LocalOwnership, `PV_LIB_SPEC_MemoryHistory12, `PV_LIB_SPEC_Native13, `PV_LIB_SPEC_NativeBindings12, `PV_LIB_SPEC_NativeBoolArc, `PV_LIB_SPEC_NativeBoolRuntime, `PV_LIB_SPEC_NativeChecks14]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_InitializedWords13.counter, `PV_LIB_SPEC_InitializedWords13.counter_bytes, `PV_LIB_SPEC_InitializedWords13.id_value, `PV_LIB_SPEC_InitializedWords13.inner, `PV_LIB_SPEC_InitializedWords13.one, `PV_LIB_SPEC_InitializedWords13.tls, `PV_LIB_SPEC_InitializedWords13.tls_bytes, `PV_LIB_SPEC_JointPremises.EntryMachinePremises, `PV_LIB_SPEC_JointPremises.NativeFacets, `PV_LIB_SPEC_JointPremises.TableRequirement, `PV_LIB_SPEC_JointPremises.entryMachine, `PV_LIB_SPEC_JointPremises.nativeFacets, `PV_LIB_SPEC_JointPremises.withTable, `PV_LIB_SPEC_LaneAJoins16.BodyEntry, `PV_LIB_SPEC_LaneAJoins16.F361ToInit, `PV_LIB_SPEC_LaneAJoins16.F6ToRange, `PV_LIB_SPEC_LaneAJoins16.Joins, `PV_LIB_SPEC_LaneAJoins16.OriginalToF6, `PV_LIB_SPEC_LaneAJoins16.RangeEntry, `PV_LIB_SPEC_LaneAJoins16.RangeToF361, `PV_LIB_SPEC_LaneAJoins16.history, `PV_LIB_SPEC_LaneAJoins16.original85, `PV_LIB_SPEC_LaneAJoins18.BodyEntry, `PV_LIB_SPEC_LaneAJoins18.F361ToInit, `PV_LIB_SPEC_LaneAJoins18.F6ToRange, `PV_LIB_SPEC_LaneAJoins18.Joins, `PV_LIB_SPEC_LaneAJoins18.OriginalToF6, `PV_LIB_SPEC_LaneAJoins18.RangeEntry, `PV_LIB_SPEC_LaneAJoins18.RangeToF361, `PV_LIB_SPEC_LaneAJoins18.history, `PV_LIB_SPEC_LaneAJoins18.original85, `PV_LIB_SPEC_LaneAJoins19.BodyEntry, `PV_LIB_SPEC_LaneAJoins19.F361ToInit, `PV_LIB_SPEC_LaneAJoins19.F6ToRange, `PV_LIB_SPEC_LaneAJoins19.Joins, `PV_LIB_SPEC_LaneAJoins19.OriginalToF6, `PV_LIB_SPEC_LaneAJoins19.RangeEntry, `PV_LIB_SPEC_LaneAJoins19.RangeToF361, `PV_LIB_SPEC_LaneAJoins19.history, `PV_LIB_SPEC_LaneAJoins19.original85, `PV_LIB_SPEC_LaneAStoreInput.actions, `PV_LIB_SPEC_LaneAStoreInput.advance, `PV_LIB_SPEC_LaneAStoreInput.coverage, `PV_LIB_SPEC_LaneAStoreInput.exact_table, `PV_LIB_SPEC_LaneAStoreInput.interpret, `PV_LIB_SPEC_LaneAStoreInput.limits, `PV_LIB_SPEC_LaneAStoreInput.step, `PV_LIB_SPEC_LocalInitMemory.no_callback_destination, `PV_LIB_SPEC_LocalInitMemory.successful, `PV_LIB_SPEC_LocalOwnership.C, `PV_LIB_SPEC_LocalOwnership.H, `PV_LIB_SPEC_LocalOwnership.K, `PV_LIB_SPEC_LocalOwnership.P, `PV_LIB_SPEC_LocalOwnership.allocated, `PV_LIB_SPEC_LocalOwnership.allocationReply, `PV_LIB_SPEC_LocalOwnership.allocationStore, `PV_LIB_SPEC_LocalOwnership.applied, `PV_LIB_SPEC_LocalOwnership.before, `PV_LIB_SPEC_LocalOwnership.data, `PV_LIB_SPEC_LocalOwnership.encode, `PV_LIB_SPEC_LocalOwnership.fresh, `PV_LIB_SPEC_LocalOwnership.granted, `PV_LIB_SPEC_LocalOwnership.handle, `PV_LIB_SPEC_LocalOwnership.index]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_LocalOwnership.loadBias, `PV_LIB_SPEC_LocalOwnership.metadata, `PV_LIB_SPEC_LocalOwnership.old_range, `PV_LIB_SPEC_LocalOwnership.ownership_export, `PV_LIB_SPEC_LocalOwnership.payload, `PV_LIB_SPEC_LocalOwnership.post, `PV_LIB_SPEC_LocalOwnership.pre, `PV_LIB_SPEC_LocalOwnership.q, `PV_LIB_SPEC_LocalOwnership.ready, `PV_LIB_SPEC_LocalOwnership.readyStore, `PV_LIB_SPEC_LocalOwnership.registered, `PV_LIB_SPEC_LocalOwnership.sourceStore, `PV_LIB_SPEC_LocalOwnership.words, `PV_LIB_SPEC_MemoryHistory12.initial, `PV_LIB_SPEC_MemoryHistory12.original, `PV_LIB_SPEC_MemoryHistory12.run, `PV_LIB_SPEC_MemoryHistory12.step, `PV_LIB_SPEC_Native13.Cut, `PV_LIB_SPEC_Native13.actions, `PV_LIB_SPEC_Native13.answer, `PV_LIB_SPEC_Native13.control, `PV_LIB_SPEC_Native13.core, `PV_LIB_SPEC_Native13.handler, `PV_LIB_SPEC_Native13.ordinary_framed, `PV_LIB_SPEC_Native13.preserves_owner_away, `PV_LIB_SPEC_Native13.run, `PV_LIB_SPEC_Native13.step, `PV_LIB_SPEC_Native13.transition, `PV_LIB_SPEC_NativeBindings12.actions, `PV_LIB_SPEC_NativeBindings12.answer, `PV_LIB_SPEC_NativeBindings12.control, `PV_LIB_SPEC_NativeBindings12.core, `PV_LIB_SPEC_NativeBindings12.handler, `PV_LIB_SPEC_NativeBindings12.isArc, `PV_LIB_SPEC_NativeBindings12.ordinary_framed, `PV_LIB_SPEC_NativeBindings12.preserves_owner_away, `PV_LIB_SPEC_NativeBindings12.run, `PV_LIB_SPEC_NativeBindings12.step, `PV_LIB_SPEC_NativeBindings12.transition, `PV_LIB_SPEC_NativeBoolArc.SiteType, `PV_LIB_SPEC_NativeBoolArc.classify, `PV_LIB_SPEC_NativeBoolArc.handler, `PV_LIB_SPEC_NativeBoolArc.image, `PV_LIB_SPEC_NativeBoolArc.layout_distinct, `PV_LIB_SPEC_NativeBoolArc.packet_classified, `PV_LIB_SPEC_NativeBoolArc.reply, `PV_LIB_SPEC_NativeBoolArc.returned_owned, `PV_LIB_SPEC_NativeBoolArc.scopeWord, `PV_LIB_SPEC_NativeBoolArc.scope_classified, `PV_LIB_SPEC_NativeBoolArc.scope_image_u8, `PV_LIB_SPEC_NativeBoolArc.scope_image_word, `PV_LIB_SPEC_NativeBoolArc.shape, `PV_LIB_SPEC_NativeBoolArc.threadWord, `PV_LIB_SPEC_NativeBoolArc.thread_word, `PV_LIB_SPEC_NativeBoolRuntime.answer, `PV_LIB_SPEC_NativeBoolRuntime.handler, `PV_LIB_SPEC_NativeBoolRuntime.invalidPure, `PV_LIB_SPEC_NativeBoolRuntime.native, `PV_LIB_SPEC_NativeBoolRuntime.ordinary_framed, `PV_LIB_SPEC_NativeBoolRuntime.valueAnswer, `PV_LIB_SPEC_NativeChecks14.arguments]
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
