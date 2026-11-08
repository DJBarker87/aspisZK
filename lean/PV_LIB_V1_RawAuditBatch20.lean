import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_F170PackagePair, `PV_LIB_SPEC_F17Entry14, `PV_LIB_SPEC_F17Full, `PV_LIB_SPEC_F17PackageComparison, `PV_LIB_SPEC_F1Arithmetic14, `PV_LIB_SPEC_F1Force14, `PV_LIB_SPEC_F1Full, `PV_LIB_SPEC_F1Prefix14, `PV_LIB_SPEC_F208Full, `PV_LIB_SPEC_F208Whole, `PV_LIB_SPEC_F219Full, `PV_LIB_SPEC_F220Full, `PV_LIB_SPEC_F270Full, `PV_LIB_SPEC_F270Whole, `PV_LIB_SPEC_F2Full, `PV_LIB_SPEC_F2PackageComparison, `PV_LIB_SPEC_F316Callback, `PV_LIB_SPEC_F316Full, `PV_LIB_SPEC_F318Full, `PV_LIB_SPEC_F361ArcMachineGap]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_F170PackagePair.PackageContract, `PV_LIB_SPEC_F170PackagePair.PackageMachineSpec, `PV_LIB_SPEC_F170PackagePair.PackagePost, `PV_LIB_SPEC_F170PackagePair.PackagePre, `PV_LIB_SPEC_F17Entry14.after, `PV_LIB_SPEC_F17Entry14.enter, `PV_LIB_SPEC_F17Entry14.site, `PV_LIB_SPEC_F17Full.Comparison, `PV_LIB_SPEC_F17Full.Contract, `PV_LIB_SPEC_F17Full.Input, `PV_LIB_SPEC_F17Full.MachineSpec, `PV_LIB_SPEC_F17Full.Post, `PV_LIB_SPEC_F17Full.Pre, `PV_LIB_SPEC_F17PackageComparison.Comparison, `PV_LIB_SPEC_F17PackageComparison.PackageContract, `PV_LIB_SPEC_F17PackageComparison.PackageMachineSpec, `PV_LIB_SPEC_F17PackageComparison.PackagePost, `PV_LIB_SPEC_F17PackageComparison.PackagePre, `PV_LIB_SPEC_F1Arithmetic14.after, `PV_LIB_SPEC_F1Arithmetic14.comparison, `PV_LIB_SPEC_F1Arithmetic14.issued, `PV_LIB_SPEC_F1Arithmetic14.original, `PV_LIB_SPEC_F1Arithmetic14.parents, `PV_LIB_SPEC_F1Arithmetic14.stage, `PV_LIB_SPEC_F1Arithmetic14.store, `PV_LIB_SPEC_F1Force14.after, `PV_LIB_SPEC_F1Force14.forced, `PV_LIB_SPEC_F1Force14.original, `PV_LIB_SPEC_F1Force14.store, `PV_LIB_SPEC_F1Full.Comparison, `PV_LIB_SPEC_F1Full.Contract, `PV_LIB_SPEC_F1Full.Input, `PV_LIB_SPEC_F1Full.MachineSpec, `PV_LIB_SPEC_F1Full.PackageStatement, `PV_LIB_SPEC_F1Full.Post, `PV_LIB_SPEC_F1Full.Pre, `PV_LIB_SPEC_F1Prefix14.after, `PV_LIB_SPEC_F1Prefix14.original, `PV_LIB_SPEC_F1Prefix14.prepare, `PV_LIB_SPEC_F1Prefix14.start, `PV_LIB_SPEC_F208Full.Comparison, `PV_LIB_SPEC_F208Full.Contract, `PV_LIB_SPEC_F208Full.Input, `PV_LIB_SPEC_F208Full.MachineSpec, `PV_LIB_SPEC_F208Full.PackageStatement, `PV_LIB_SPEC_F208Full.Post, `PV_LIB_SPEC_F208Full.Pre, `PV_LIB_SPEC_F208Whole.Comparison, `PV_LIB_SPEC_F208Whole.Contract, `PV_LIB_SPEC_F208Whole.Input, `PV_LIB_SPEC_F208Whole.MachineSpec, `PV_LIB_SPEC_F208Whole.PackageStatement, `PV_LIB_SPEC_F208Whole.Post, `PV_LIB_SPEC_F208Whole.Pre, `PV_LIB_SPEC_F219Full.Comparison, `PV_LIB_SPEC_F219Full.Contract, `PV_LIB_SPEC_F219Full.Input, `PV_LIB_SPEC_F219Full.MachineSpec, `PV_LIB_SPEC_F219Full.PackageStatement, `PV_LIB_SPEC_F219Full.Post, `PV_LIB_SPEC_F219Full.Pre, `PV_LIB_SPEC_F220Full.Comparison, `PV_LIB_SPEC_F220Full.Contract, `PV_LIB_SPEC_F220Full.Input]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_F220Full.MachineSpec, `PV_LIB_SPEC_F220Full.PackageStatement, `PV_LIB_SPEC_F220Full.Post, `PV_LIB_SPEC_F220Full.Pre, `PV_LIB_SPEC_F270Full.Comparison, `PV_LIB_SPEC_F270Full.Contract, `PV_LIB_SPEC_F270Full.Input, `PV_LIB_SPEC_F270Full.MachineSpec, `PV_LIB_SPEC_F270Full.PackageStatement, `PV_LIB_SPEC_F270Full.Post, `PV_LIB_SPEC_F270Full.Pre, `PV_LIB_SPEC_F270Whole.Comparison, `PV_LIB_SPEC_F270Whole.Contract, `PV_LIB_SPEC_F270Whole.Input, `PV_LIB_SPEC_F270Whole.MachineSpec, `PV_LIB_SPEC_F270Whole.PackageStatement, `PV_LIB_SPEC_F270Whole.Post, `PV_LIB_SPEC_F270Whole.Pre, `PV_LIB_SPEC_F2Full.Comparison, `PV_LIB_SPEC_F2Full.Contract, `PV_LIB_SPEC_F2Full.Input, `PV_LIB_SPEC_F2Full.MachineSpec, `PV_LIB_SPEC_F2Full.Post, `PV_LIB_SPEC_F2Full.Pre, `PV_LIB_SPEC_F2PackageComparison.Comparison, `PV_LIB_SPEC_F2PackageComparison.PackageContract, `PV_LIB_SPEC_F2PackageComparison.PackageMachineSpec, `PV_LIB_SPEC_F2PackageComparison.PackagePost, `PV_LIB_SPEC_F2PackageComparison.PackagePre, `PV_LIB_SPEC_F316Callback.Comparison, `PV_LIB_SPEC_F316Callback.Contract, `PV_LIB_SPEC_F316Callback.Frame, `PV_LIB_SPEC_F316Callback.Input, `PV_LIB_SPEC_F316Callback.MachineSpec, `PV_LIB_SPEC_F316Callback.Post, `PV_LIB_SPEC_F316Callback.Pre, `PV_LIB_SPEC_F316Callback.ReturnDestination, `PV_LIB_SPEC_F316Callback.entry, `PV_LIB_SPEC_F316Callback.intrinsicInput, `PV_LIB_SPEC_F316Callback.ordinaryInput, `PV_LIB_SPEC_F316Callback.view, `PV_LIB_SPEC_F316Full.Comparison, `PV_LIB_SPEC_F316Full.Contract, `PV_LIB_SPEC_F316Full.Input, `PV_LIB_SPEC_F316Full.MachineSpec, `PV_LIB_SPEC_F316Full.PackageStatement, `PV_LIB_SPEC_F316Full.Post, `PV_LIB_SPEC_F316Full.Pre, `PV_LIB_SPEC_F318Full.Boundary, `PV_LIB_SPEC_F318Full.Comparison, `PV_LIB_SPEC_F318Full.Contract, `PV_LIB_SPEC_F318Full.Delivered, `PV_LIB_SPEC_F318Full.First, `PV_LIB_SPEC_F318Full.Input, `PV_LIB_SPEC_F318Full.MachineSpec, `PV_LIB_SPEC_F318Full.PackageStatement, `PV_LIB_SPEC_F318Full.Post, `PV_LIB_SPEC_F318Full.Pre, `PV_LIB_SPEC_F318Full.entry, `PV_LIB_SPEC_F361ArcMachineGap.Event, `PV_LIB_SPEC_F361ArcMachineGap.Machine]
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
