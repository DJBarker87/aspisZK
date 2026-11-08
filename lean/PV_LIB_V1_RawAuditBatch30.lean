import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_TlsAt67, `PV_LIB_SPEC_TlsAt68, `PV_LIB_SPEC_TlsAt75, `PV_LIB_SPEC_TlsAt84, `PV_LIB_SPEC_TlsAt85, `PV_LIB_SPEC_TlsBindings13, `PV_LIB_SPEC_TlsBound15, `PV_LIB_SPEC_TlsCallable16, `PV_LIB_SPEC_TlsCallableHistory16, `PV_LIB_SPEC_TlsCallableLift16, `PV_LIB_SPEC_TlsDelivery15, `PV_LIB_SPEC_TlsEntry14, `PV_LIB_SPEC_TlsForward16, `PV_LIB_SPEC_TlsForwardLift16, `PV_LIB_SPEC_TlsLoad15, `PV_LIB_SPEC_TlsNative15, `PV_LIB_SPEC_TlsNone15, `PV_LIB_SPEC_TlsOriginal14, `PV_LIB_SPEC_TlsOriginal15, `PV_LIB_SPEC_TlsPoll15, `PV_LIB_SPEC_TlsRecheck13, `PV_LIB_SPEC_TlsRequest15, `PV_LIB_SPEC_ToVec]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_TlsAt67.handler, `PV_LIB_SPEC_TlsAt67.issued67, `PV_LIB_SPEC_TlsAt67.original67, `PV_LIB_SPEC_TlsAt67.result_bound, `PV_LIB_SPEC_TlsAt67.state67, `PV_LIB_SPEC_TlsAt67.world67, `PV_LIB_SPEC_TlsAt68.consume, `PV_LIB_SPEC_TlsAt68.context, `PV_LIB_SPEC_TlsAt68.original68, `PV_LIB_SPEC_TlsAt75.at75, `PV_LIB_SPEC_TlsAt75.cell, `PV_LIB_SPEC_TlsAt75.consumed75, `PV_LIB_SPEC_TlsAt75.handler, `PV_LIB_SPEC_TlsAt75.original75, `PV_LIB_SPEC_TlsAt75.state75, `PV_LIB_SPEC_TlsAt75.store75, `PV_LIB_SPEC_TlsAt84.at84, `PV_LIB_SPEC_TlsAt84.config, `PV_LIB_SPEC_TlsAt84.consumed84, `PV_LIB_SPEC_TlsAt84.dereference, `PV_LIB_SPEC_TlsAt84.issued84, `PV_LIB_SPEC_TlsAt84.original84, `PV_LIB_SPEC_TlsAt84.stage75, `PV_LIB_SPEC_TlsAt84.state84, `PV_LIB_SPEC_TlsAt85.consume, `PV_LIB_SPEC_TlsAt85.context, `PV_LIB_SPEC_TlsAt85.original85, `PV_LIB_SPEC_TlsBindings13.Slot, `PV_LIB_SPEC_TlsBindings13.read, `PV_LIB_SPEC_TlsBindings13.reply, `PV_LIB_SPEC_TlsBindings13.selected, `PV_LIB_SPEC_TlsBindings13.value, `PV_LIB_SPEC_TlsBindings13.world, `PV_LIB_SPEC_TlsBound15.answer, `PV_LIB_SPEC_TlsBound15.different, `PV_LIB_SPEC_TlsBound15.parameters, `PV_LIB_SPEC_TlsBound15.selected, `PV_LIB_SPEC_TlsBound15.trigger, `PV_LIB_SPEC_TlsCallable16.config, `PV_LIB_SPEC_TlsCallable16.source, `PV_LIB_SPEC_TlsCallable16.trace, `PV_LIB_SPEC_TlsCallableHistory16.issued, `PV_LIB_SPEC_TlsCallableHistory16.site, `PV_LIB_SPEC_TlsCallableLift16.clear, `PV_LIB_SPEC_TlsCallableLift16.source, `PV_LIB_SPEC_TlsDelivery15.after, `PV_LIB_SPEC_TlsDelivery15.store55, `PV_LIB_SPEC_TlsDelivery15.transition, `PV_LIB_SPEC_TlsEntry14.after, `PV_LIB_SPEC_TlsEntry14.enter, `PV_LIB_SPEC_TlsEntry14.key, `PV_LIB_SPEC_TlsEntry14.site, `PV_LIB_SPEC_TlsForward16.prepared, `PV_LIB_SPEC_TlsForward16.source, `PV_LIB_SPEC_TlsForward16.trace, `PV_LIB_SPEC_TlsForwardLift16.clear, `PV_LIB_SPEC_TlsForwardLift16.source, `PV_LIB_SPEC_TlsLoad15.after, `PV_LIB_SPEC_TlsLoad15.load, `PV_LIB_SPEC_TlsNative15.active, `PV_LIB_SPEC_TlsNative15.cut, `PV_LIB_SPEC_TlsNative15.physical, `PV_LIB_SPEC_TlsNative15.reference, `PV_LIB_SPEC_TlsNative15.request]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_TlsNative15.source, `PV_LIB_SPEC_TlsNative15.value, `PV_LIB_SPEC_TlsNone15.after, `PV_LIB_SPEC_TlsNone15.construct, `PV_LIB_SPEC_TlsNone15.kind, `PV_LIB_SPEC_TlsOriginal14.atTryWith, `PV_LIB_SPEC_TlsOriginal14.no_native40, `PV_LIB_SPEC_TlsOriginal14.original32, `PV_LIB_SPEC_TlsOriginal14.original40, `PV_LIB_SPEC_TlsOriginal14.withIssued, `PV_LIB_SPEC_TlsOriginal14.withParents, `PV_LIB_SPEC_TlsOriginal14.withStore, `PV_LIB_SPEC_TlsOriginal14.workerIssued, `PV_LIB_SPEC_TlsOriginal14.workerParents, `PV_LIB_SPEC_TlsOriginal14.workerStore, `PV_LIB_SPEC_TlsOriginal14.world40, `PV_LIB_SPEC_TlsOriginal15.issued, `PV_LIB_SPEC_TlsOriginal15.key_bound, `PV_LIB_SPEC_TlsOriginal15.key_read, `PV_LIB_SPEC_TlsOriginal15.original50, `PV_LIB_SPEC_TlsOriginal15.original51, `PV_LIB_SPEC_TlsOriginal15.parents, `PV_LIB_SPEC_TlsOriginal15.store40, `PV_LIB_SPEC_TlsOriginal15.store50, `PV_LIB_SPEC_TlsPoll15.after, `PV_LIB_SPEC_TlsPoll15.kind, `PV_LIB_SPEC_TlsPoll15.prepare, `PV_LIB_SPEC_TlsPoll15.prepared, `PV_LIB_SPEC_TlsRecheck13.config, `PV_LIB_SPEC_TlsRecheck13.getter, `PV_LIB_SPEC_TlsRecheck13.getter_reply, `PV_LIB_SPEC_TlsRecheck13.getter_selected, `PV_LIB_SPEC_TlsRecheck13.getter_value, `PV_LIB_SPEC_TlsRecheck13.init, `PV_LIB_SPEC_TlsRecheck13.initializer, `PV_LIB_SPEC_TlsRequest15.after, `PV_LIB_SPEC_TlsRequest15.issuedStore, `PV_LIB_SPEC_TlsRequest15.request, `PV_LIB_SPEC_TlsRequest15.site, `PV_LIB_SPEC_ToVec.Boundary, `PV_LIB_SPEC_ToVec.Contract, `PV_LIB_SPEC_ToVec.Entry, `PV_LIB_SPEC_ToVec.Event, `PV_LIB_SPEC_ToVec.First, `PV_LIB_SPEC_ToVec.Frame, `PV_LIB_SPEC_ToVec.Machine, `PV_LIB_SPEC_ToVec.MachineSpec, `PV_LIB_SPEC_ToVec.Observation, `PV_LIB_SPEC_ToVec.Old.Entry, `PV_LIB_SPEC_ToVec.Old.Machine, `PV_LIB_SPEC_ToVec.Outcome, `PV_LIB_SPEC_ToVec.Pending, `PV_LIB_SPEC_ToVec.Post, `PV_LIB_SPEC_ToVec.Pre, `PV_LIB_SPEC_ToVec.abort_prefix, `PV_LIB_SPEC_ToVec.execution, `PV_LIB_SPEC_ToVec.first_unique, `PV_LIB_SPEC_ToVec.no_false_pending11, `PV_LIB_SPEC_ToVec.observe, `PV_LIB_SPEC_ToVec.pending_implies_old, `PV_LIB_SPEC_ToVec.pre_same]
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
