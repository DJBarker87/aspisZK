import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_OwnInitEntry, `PV_LIB_SPEC_OwnInitFull, `PV_LIB_SPEC_PhysicalStack12, `PV_LIB_SPEC_Prefix54World18, `PV_LIB_SPEC_PrefixEnvironment13, `PV_LIB_SPEC_PrefixEnvironment14, `PV_LIB_SPEC_PrefixHistory13, `PV_LIB_SPEC_PrefixNative13, `PV_LIB_SPEC_PrefixNative14, `PV_LIB_SPEC_PreludeValues14, `PV_LIB_SPEC_RawBinding14, `PV_LIB_SPEC_RawVec14, `PV_LIB_SPEC_ReachedEnvironment14]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_OwnInitEntry.closure, `PV_LIB_SPEC_OwnInitEntry.entry_nonempty, `PV_LIB_SPEC_OwnInitEntry.fHeader, `PV_LIB_SPEC_OwnInitEntry.f_typed, `PV_LIB_SPEC_OwnInitEntry.nHeader, `PV_LIB_SPEC_OwnInitEntry.n_bytes, `PV_LIB_SPEC_OwnInitEntry.n_typed, `PV_LIB_SPEC_OwnInitEntry.places, `PV_LIB_SPEC_OwnInitEntry.receivers, `PV_LIB_SPEC_OwnInitEntry.runHeader, `PV_LIB_SPEC_OwnInitEntry.run_bytes, `PV_LIB_SPEC_OwnInitEntry.run_typed, `PV_LIB_SPEC_OwnInitEntry.site, `PV_LIB_SPEC_OwnInitEntry.state, `PV_LIB_SPEC_OwnInitEntry.taskHeader, `PV_LIB_SPEC_OwnInitEntry.tasks_typed, `PV_LIB_SPEC_OwnInitEntry.zero, `PV_LIB_SPEC_OwnInitFull.AllocationExport, `PV_LIB_SPEC_OwnInitFull.AllocationWitness, `PV_LIB_SPEC_OwnInitFull.Boundary, `PV_LIB_SPEC_OwnInitFull.Comparison, `PV_LIB_SPEC_OwnInitFull.Contract, `PV_LIB_SPEC_OwnInitFull.First, `PV_LIB_SPEC_OwnInitFull.InitPoll, `PV_LIB_SPEC_OwnInitFull.Input, `PV_LIB_SPEC_OwnInitFull.LegacySome, `PV_LIB_SPEC_OwnInitFull.MachineSpec, `PV_LIB_SPEC_OwnInitFull.OwnershipExport, `PV_LIB_SPEC_OwnInitFull.Post, `PV_LIB_SPEC_OwnInitFull.Pre, `PV_LIB_SPEC_OwnInitFull.Representation, `PV_LIB_SPEC_OwnInitFull.entry, `PV_LIB_SPEC_PhysicalStack12.Frame, `PV_LIB_SPEC_PhysicalStack12.captureWords, `PV_LIB_SPEC_PhysicalStack12.copies_default, `PV_LIB_SPEC_PhysicalStack12.defaultHooks, `PV_LIB_SPEC_PhysicalStack12.default_mask, `PV_LIB_SPEC_PhysicalStack12.default_snapshot, `PV_LIB_SPEC_PhysicalStack12.installDefault, `PV_LIB_SPEC_PhysicalStack12.localConfig, `PV_LIB_SPEC_PhysicalStack12.localFrame, `PV_LIB_SPEC_PhysicalStack12.local_capture, `PV_LIB_SPEC_PhysicalStack12.local_resolved, `PV_LIB_SPEC_PhysicalStack12.physical, `PV_LIB_SPEC_PhysicalStack12.registers, `PV_LIB_SPEC_PhysicalStack12.stack_ghost, `PV_LIB_SPEC_Prefix54World18.original13, `PV_LIB_SPEC_Prefix54World18.original16, `PV_LIB_SPEC_Prefix54World18.original22, `PV_LIB_SPEC_Prefix54World18.original25, `PV_LIB_SPEC_Prefix54World18.original32, `PV_LIB_SPEC_Prefix54World18.original40, `PV_LIB_SPEC_Prefix54World18.original50, `PV_LIB_SPEC_Prefix54World18.original51, `PV_LIB_SPEC_Prefix54World18.original53, `PV_LIB_SPEC_Prefix54World18.original54, `PV_LIB_SPEC_Prefix54World18.original6, `PV_LIB_SPEC_Prefix54World18.original7, `PV_LIB_SPEC_PrefixEnvironment13.allocations, `PV_LIB_SPEC_PrefixEnvironment13.environment, `PV_LIB_SPEC_PrefixEnvironment13.native, `PV_LIB_SPEC_PrefixEnvironment13.parameters, `PV_LIB_SPEC_PrefixEnvironment13.pre, `PV_LIB_SPEC_PrefixEnvironment14.allocations]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_PrefixEnvironment14.environment, `PV_LIB_SPEC_PrefixEnvironment14.native, `PV_LIB_SPEC_PrefixEnvironment14.parameters, `PV_LIB_SPEC_PrefixEnvironment14.pre, `PV_LIB_SPEC_PrefixHistory13.initial, `PV_LIB_SPEC_PrefixHistory13.original, `PV_LIB_SPEC_PrefixHistory13.run, `PV_LIB_SPEC_PrefixHistory13.step, `PV_LIB_SPEC_PrefixNative13.Cut, `PV_LIB_SPEC_PrefixNative13.actions, `PV_LIB_SPEC_PrefixNative13.answer, `PV_LIB_SPEC_PrefixNative13.control, `PV_LIB_SPEC_PrefixNative13.core, `PV_LIB_SPEC_PrefixNative13.handler, `PV_LIB_SPEC_PrefixNative13.ordinary_framed, `PV_LIB_SPEC_PrefixNative13.preserves_owner_away, `PV_LIB_SPEC_PrefixNative13.run, `PV_LIB_SPEC_PrefixNative13.step, `PV_LIB_SPEC_PrefixNative13.transition, `PV_LIB_SPEC_PrefixNative14.Cut, `PV_LIB_SPEC_PrefixNative14.actions, `PV_LIB_SPEC_PrefixNative14.answer, `PV_LIB_SPEC_PrefixNative14.control, `PV_LIB_SPEC_PrefixNative14.core, `PV_LIB_SPEC_PrefixNative14.handler, `PV_LIB_SPEC_PrefixNative14.ordinary_framed, `PV_LIB_SPEC_PrefixNative14.preserves_owner_away, `PV_LIB_SPEC_PrefixNative14.run, `PV_LIB_SPEC_PrefixNative14.step, `PV_LIB_SPEC_PrefixNative14.transition, `PV_LIB_SPEC_PreludeValues14.arguments, `PV_LIB_SPEC_PreludeValues14.config, `PV_LIB_SPEC_PreludeValues14.fn164, `PV_LIB_SPEC_PreludeValues14.fn165, `PV_LIB_SPEC_PreludeValues14.fn93, `PV_LIB_SPEC_PreludeValues14.next, `PV_LIB_SPEC_PreludeValues14.none_tag, `PV_LIB_SPEC_PreludeValues14.other, `PV_LIB_SPEC_PreludeValues14.rangeKind, `PV_LIB_SPEC_PreludeValues14.range_next, `PV_LIB_SPEC_PreludeValues14.raw, `PV_LIB_SPEC_PreludeValues14.reply, `PV_LIB_SPEC_PreludeValues14.sizeKind, `PV_LIB_SPEC_PreludeValues14.some_tag, `PV_LIB_SPEC_PreludeValues14.value, `PV_LIB_SPEC_PreludeValues14.vector, `PV_LIB_SPEC_RawBinding14.at268, `PV_LIB_SPEC_RawBinding14.bound268, `PV_LIB_SPEC_RawBinding14.inline164, `PV_LIB_SPEC_RawVec14.dispatch, `PV_LIB_SPEC_RawVec14.fields, `PV_LIB_SPEC_RawVec14.inner, `PV_LIB_SPEC_RawVec14.markerKind, `PV_LIB_SPEC_RawVec14.rawKind, `PV_LIB_SPEC_RawVec14.reply, `PV_LIB_SPEC_RawVec14.token, `PV_LIB_SPEC_RawVec14.value, `PV_LIB_SPEC_ReachedEnvironment14.allocations, `PV_LIB_SPEC_ReachedEnvironment14.environment, `PV_LIB_SPEC_ReachedEnvironment14.native, `PV_LIB_SPEC_ReachedEnvironment14.parameters]
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
