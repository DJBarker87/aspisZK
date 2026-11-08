import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_F361Full, `PV_LIB_SPEC_FrozenABI, `PV_LIB_SPEC_History13, `PV_LIB_SPEC_History18, `PV_LIB_SPEC_HistoryInvariant, `PV_LIB_SPEC_HookKinds14, `PV_LIB_SPEC_InitImageRecheck, `PV_LIB_SPEC_ThreadSpecifications]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_Frozen.F2.Comparison, `PV_LIB_SPEC_Frozen.F2.Contract, `PV_LIB_SPEC_Frozen.F2.Input, `PV_LIB_SPEC_Frozen.F2.MachineSpec, `PV_LIB_SPEC_Frozen.F2.Post, `PV_LIB_SPEC_Frozen.F2.Pre, `PV_LIB_SPEC_Frozen.F208.Comparison, `PV_LIB_SPEC_Frozen.F208.Contract, `PV_LIB_SPEC_Frozen.F208.Input, `PV_LIB_SPEC_Frozen.F208.MachineSpec, `PV_LIB_SPEC_Frozen.F208.Post, `PV_LIB_SPEC_Frozen.F208.Pre, `PV_LIB_SPEC_Frozen.F219.Comparison, `PV_LIB_SPEC_Frozen.F219.Contract, `PV_LIB_SPEC_Frozen.F219.Input, `PV_LIB_SPEC_Frozen.F219.MachineSpec, `PV_LIB_SPEC_Frozen.F219.Post, `PV_LIB_SPEC_Frozen.F219.Pre, `PV_LIB_SPEC_Frozen.F220.Comparison, `PV_LIB_SPEC_Frozen.F220.Contract, `PV_LIB_SPEC_Frozen.F220.Input, `PV_LIB_SPEC_Frozen.F220.MachineSpec, `PV_LIB_SPEC_Frozen.F220.Post, `PV_LIB_SPEC_Frozen.F220.Pre, `PV_LIB_SPEC_Frozen.F270.Comparison, `PV_LIB_SPEC_Frozen.F270.Contract, `PV_LIB_SPEC_Frozen.F270.Input, `PV_LIB_SPEC_Frozen.F270.MachineSpec, `PV_LIB_SPEC_Frozen.F270.Post, `PV_LIB_SPEC_Frozen.F270.Pre, `PV_LIB_SPEC_Frozen.F316.Comparison, `PV_LIB_SPEC_Frozen.F316.Contract, `PV_LIB_SPEC_Frozen.F316.Input, `PV_LIB_SPEC_Frozen.F316.MachineSpec, `PV_LIB_SPEC_Frozen.F316.Post, `PV_LIB_SPEC_Frozen.F316.Pre, `PV_LIB_SPEC_Frozen.F318.Boundary, `PV_LIB_SPEC_Frozen.F318.Comparison, `PV_LIB_SPEC_Frozen.F318.Contract, `PV_LIB_SPEC_Frozen.F318.First, `PV_LIB_SPEC_Frozen.F318.Input, `PV_LIB_SPEC_Frozen.F318.MachineSpec, `PV_LIB_SPEC_Frozen.F318.Post, `PV_LIB_SPEC_Frozen.F318.Pre, `PV_LIB_SPEC_Frozen.F318.entry, `PV_LIB_SPEC_Frozen.F361.Comparison, `PV_LIB_SPEC_Frozen.F361.Contract, `PV_LIB_SPEC_Frozen.F361.Input, `PV_LIB_SPEC_Frozen.F361.MachineSpec, `PV_LIB_SPEC_Frozen.F361.PackagePost, `PV_LIB_SPEC_Frozen.F361.PackagePre, `PV_LIB_SPEC_Frozen.F361.Post, `PV_LIB_SPEC_Frozen.F361.Pre, `PV_LIB_SPEC_Frozen.F361.Representation, `PV_LIB_SPEC_Frozen.F361.view, `PV_LIB_SPEC_Frozen.F5.Comparison, `PV_LIB_SPEC_Frozen.F5.Contract, `PV_LIB_SPEC_Frozen.F5.Input, `PV_LIB_SPEC_Frozen.F5.MachineSpec, `PV_LIB_SPEC_Frozen.F5.Post, `PV_LIB_SPEC_Frozen.F5.Pre, `PV_LIB_SPEC_Frozen.F6.Comparison, `PV_LIB_SPEC_Frozen.F6.Contract, `PV_LIB_SPEC_Frozen.F6.Input]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_Frozen.F6.MachineSpec, `PV_LIB_SPEC_Frozen.F6.Post, `PV_LIB_SPEC_Frozen.F6.Pre, `PV_LIB_SPEC_Frozen.MachineSpec, `PV_LIB_SPEC_Frozen.OwnInit.Comparison, `PV_LIB_SPEC_Frozen.OwnInit.Contract, `PV_LIB_SPEC_Frozen.OwnInit.Input, `PV_LIB_SPEC_Frozen.OwnInit.MachineSpec, `PV_LIB_SPEC_Frozen.OwnInit.Post, `PV_LIB_SPEC_Frozen.OwnInit.Pre, `PV_LIB_SPEC_Frozen.OwnInit.representation, `PV_LIB_SPEC_Frozen.Parameters, `PV_LIB_SPEC_Frozen.References, `PV_LIB_SPEC_Frozen.ResourceBinding, `PV_LIB_SPEC_Frozen.ResourceRequest, `PV_LIB_SPEC_Frozen.RootPre, `PV_LIB_SPEC_Frozen.runtime, `PV_LIB_SPEC_Frozen.source, `PV_LIB_SPEC_FrozenABI.atomicKind, `PV_LIB_SPEC_FrozenABI.flowType, `PV_LIB_SPEC_FrozenABI.optionType, `PV_LIB_SPEC_FrozenABI.residualType, `PV_LIB_SPEC_FrozenABI.resultType, `PV_LIB_SPEC_FrozenABI.unsafeCellKind, `PV_LIB_SPEC_Full.MachineSpec, `PV_LIB_SPEC_Full.Post, `PV_LIB_SPEC_Full.SourceAdequacy, `PV_LIB_SPEC_Full.body, `PV_LIB_SPEC_Full.programs, `PV_LIB_SPEC_Full.source, `PV_LIB_SPEC_History13.initial, `PV_LIB_SPEC_History13.original, `PV_LIB_SPEC_History13.run, `PV_LIB_SPEC_History13.step, `PV_LIB_SPEC_History18.concrete85, `PV_LIB_SPEC_History18.history, `PV_LIB_SPEC_History18.original85, `PV_LIB_SPEC_History18.rejected_overlap, `PV_LIB_SPEC_History18.replies85, `PV_LIB_SPEC_History18.scheduled_heap_away, `PV_LIB_SPEC_History18.world85, `PV_LIB_SPEC_HistoryInvariant.Invariant, `PV_LIB_SPEC_HistoryInvariant.append_record, `PV_LIB_SPEC_HistoryInvariant.context_origin, `PV_LIB_SPEC_HistoryInvariant.initial, `PV_LIB_SPEC_HistoryInvariant.original, `PV_LIB_SPEC_HistoryInvariant.record_mono, `PV_LIB_SPEC_HistoryInvariant.run, `PV_LIB_SPEC_HistoryInvariant.step, `PV_LIB_SPEC_HookKinds14.childKind, `PV_LIB_SPEC_HookKinds14.hooksKind, `PV_LIB_SPEC_HookKinds14.innerKind, `PV_LIB_SPEC_HookKinds14.markerKind, `PV_LIB_SPEC_HookKinds14.noneKind, `PV_LIB_SPEC_HookKinds14.rawKind, `PV_LIB_SPEC_HookKinds14.vectorKind, `PV_LIB_SPEC_InitImageRecheck.first, `PV_LIB_SPEC_InitImageRecheck.initPost_memory, `PV_LIB_SPEC_InitImageRecheck.memory_agreement, `PV_LIB_SPEC_InitImageRecheck.second, `PV_LIB_SPEC_InitImageRecheck.third]
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
