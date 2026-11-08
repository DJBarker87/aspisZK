import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_F270Whole, `PV_LIB_SPEC_ReachedEnvironment14, `PV_LIB_SPEC_ReachedHistory14, `PV_LIB_SPEC_ReachedNative14, `PV_LIB_SPEC_RebasedCaptures18, `PV_LIB_SPEC_RebasedEntry18, `PV_LIB_SPEC_RebasedPre18, `PV_LIB_SPEC_RegistrationGap, `PV_LIB_SPEC_ResourceHistory, `PV_LIB_SPEC_ScopeAllocationGap, `PV_LIB_SPEC_ScopeAllocationPollGap, `PV_LIB_SPEC_ScopePhysical13, `PV_LIB_SPEC_ScopeRuntimeGap, `PV_LIB_SPEC_SiteArc, `PV_LIB_SPEC_SiteArcRecheck]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_ReachedEnvironment14.pre, `PV_LIB_SPEC_ReachedHistory14.initial, `PV_LIB_SPEC_ReachedHistory14.original, `PV_LIB_SPEC_ReachedHistory14.run, `PV_LIB_SPEC_ReachedHistory14.step, `PV_LIB_SPEC_ReachedNative14.Cut, `PV_LIB_SPEC_ReachedNative14.actions, `PV_LIB_SPEC_ReachedNative14.answer, `PV_LIB_SPEC_ReachedNative14.control, `PV_LIB_SPEC_ReachedNative14.core, `PV_LIB_SPEC_ReachedNative14.handler, `PV_LIB_SPEC_ReachedNative14.ordinary_framed, `PV_LIB_SPEC_ReachedNative14.preserves_owner_away, `PV_LIB_SPEC_ReachedNative14.run, `PV_LIB_SPEC_ReachedNative14.step, `PV_LIB_SPEC_ReachedNative14.transition, `PV_LIB_SPEC_RebasedCaptures18.bytes, `PV_LIB_SPEC_RebasedCaptures18.captures, `PV_LIB_SPEC_RebasedCaptures18.closure, `PV_LIB_SPEC_RebasedCaptures18.entry_nonempty, `PV_LIB_SPEC_RebasedCaptures18.fHeader, `PV_LIB_SPEC_RebasedCaptures18.f_typed, `PV_LIB_SPEC_RebasedCaptures18.nHeader, `PV_LIB_SPEC_RebasedCaptures18.n_bytes, `PV_LIB_SPEC_RebasedCaptures18.n_typed, `PV_LIB_SPEC_RebasedCaptures18.one, `PV_LIB_SPEC_RebasedCaptures18.places, `PV_LIB_SPEC_RebasedCaptures18.receivers, `PV_LIB_SPEC_RebasedCaptures18.runHeader, `PV_LIB_SPEC_RebasedCaptures18.run_bytes, `PV_LIB_SPEC_RebasedCaptures18.run_typed, `PV_LIB_SPEC_RebasedCaptures18.site, `PV_LIB_SPEC_RebasedCaptures18.state, `PV_LIB_SPEC_RebasedCaptures18.taskHeader, `PV_LIB_SPEC_RebasedCaptures18.tasks_typed, `PV_LIB_SPEC_RebasedCaptures18.zero, `PV_LIB_SPEC_RebasedEntry18.hooksSlot, `PV_LIB_SPEC_RebasedEntry18.input, `PV_LIB_SPEC_RebasedEntry18.memory_before, `PV_LIB_SPEC_RebasedEntry18.slot, `PV_LIB_SPEC_RebasedEntry18.state, `PV_LIB_SPEC_RebasedEntry18.store, `PV_LIB_SPEC_RebasedEntry18.tlsState, `PV_LIB_SPEC_RebasedPre18.captured, `PV_LIB_SPEC_RebasedPre18.f_typed, `PV_LIB_SPEC_RebasedPre18.fresh, `PV_LIB_SPEC_RebasedPre18.memory_before, `PV_LIB_SPEC_RebasedPre18.n_bytes, `PV_LIB_SPEC_RebasedPre18.n_typed, `PV_LIB_SPEC_RebasedPre18.owner, `PV_LIB_SPEC_RebasedPre18.pre, `PV_LIB_SPEC_RebasedPre18.receivers, `PV_LIB_SPEC_RebasedPre18.run_bytes, `PV_LIB_SPEC_RebasedPre18.run_typed, `PV_LIB_SPEC_RebasedPre18.tasks_typed, `PV_LIB_SPEC_RebasedPre18.validity, `PV_LIB_SPEC_RegistrationGap.Event, `PV_LIB_SPEC_RegistrationGap.JointStep, `PV_LIB_SPEC_RegistrationGap.State, `PV_LIB_SPEC_RegistrationGap.before, `PV_LIB_SPEC_RegistrationGap.raw_next, `PV_LIB_SPEC_RegistrationGap.registered_next, `PV_LIB_SPEC_RegistrationGap.steps_differ, `PV_LIB_SPEC_ResourceHistory.Context]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_ResourceHistory.Execution, `PV_LIB_SPEC_ResourceHistory.HistoryAdequacy, `PV_LIB_SPEC_ResourceHistory.Issued, `PV_LIB_SPEC_ResourceHistory.allocationResources, `PV_LIB_SPEC_ResourceHistory.allocation_binding, `PV_LIB_SPEC_ResourceHistory.arguments, `PV_LIB_SPEC_ResourceHistory.context, `PV_LIB_SPEC_ResourceHistory.initial, `PV_LIB_SPEC_ResourceHistory.issuing, `PV_LIB_SPEC_ResourceHistory.ordinary, `PV_LIB_SPEC_ResourceHistory.recordIssue, `PV_LIB_SPEC_ResourceHistory.request, `PV_LIB_SPEC_ResourceHistory.reservationResources, `PV_LIB_SPEC_ResourceHistory.reservation_binding, `PV_LIB_SPEC_ResourceHistory.run, `PV_LIB_SPEC_ResourceHistory.step, `PV_LIB_SPEC_Row.Frame, `PV_LIB_SPEC_Row.Input, `PV_LIB_SPEC_Row.MachineSpec, `PV_LIB_SPEC_Row.Post, `PV_LIB_SPEC_Row.Pre, `PV_LIB_SPEC_Row.Reachable, `PV_LIB_SPEC_Row.ReferenceEntry, `PV_LIB_SPEC_Row.Runtime, `PV_LIB_SPEC_Row.SourceAdequacy, `PV_LIB_SPEC_Row.entry, `PV_LIB_SPEC_Row.leafEntry, `PV_LIB_SPEC_Row.source, `PV_LIB_SPEC_ScopeAllocationGap.C, `PV_LIB_SPEC_ScopeAllocationGap.K, `PV_LIB_SPEC_ScopeAllocationGap.atomic, `PV_LIB_SPEC_ScopeAllocationGap.not_an_option, `PV_LIB_SPEC_ScopeAllocationGap.scope_body, `PV_LIB_SPEC_ScopeAllocationGap.scope_decode, `PV_LIB_SPEC_ScopeAllocationGap.wrong_layout, `PV_LIB_SPEC_ScopeAllocationPollGap.correct40, `PV_LIB_SPEC_ScopeAllocationPollGap.rejects, `PV_LIB_SPEC_ScopeAllocationPollGap.request, `PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources, `PV_LIB_SPEC_ScopeAllocationPollGap.unbound48, `PV_LIB_SPEC_ScopePhysical13.one_to_two, `PV_LIB_SPEC_ScopePhysical13.operands, `PV_LIB_SPEC_ScopePhysical13.reply, `PV_LIB_SPEC_ScopeRuntimeGap.answer_none, `PV_LIB_SPEC_ScopeRuntimeGap.native_none, `PV_LIB_SPEC_ScopeRuntimeGap.parameters, `PV_LIB_SPEC_SiteArc.SiteType, `PV_LIB_SPEC_SiteArc.classify, `PV_LIB_SPEC_SiteArc.handler, `PV_LIB_SPEC_SiteArc.image, `PV_LIB_SPEC_SiteArc.layout_distinct, `PV_LIB_SPEC_SiteArc.packet_classified, `PV_LIB_SPEC_SiteArc.reply, `PV_LIB_SPEC_SiteArc.returned_owned, `PV_LIB_SPEC_SiteArc.scopeWord, `PV_LIB_SPEC_SiteArc.scope_classified, `PV_LIB_SPEC_SiteArc.shape, `PV_LIB_SPEC_SiteArc.threadWord, `PV_LIB_SPEC_SiteArcRecheck.packet_reply, `PV_LIB_SPEC_SiteArcRecheck.panic, `PV_LIB_SPEC_SiteArcRecheck.scope_handler]
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
