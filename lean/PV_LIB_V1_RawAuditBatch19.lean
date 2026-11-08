import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_DisjointPre18, `PV_LIB_SPEC_Entry13, `PV_LIB_SPEC_Entry14, `PV_LIB_SPEC_EntryPre13, `PV_LIB_SPEC_EntryPre14, `PV_LIB_SPEC_EntryWorld18, `PV_LIB_SPEC_Environment, `PV_LIB_SPEC_F0Full, `PV_LIB_SPEC_F125Full, `PV_LIB_SPEC_F15Full, `PV_LIB_SPEC_F15Whole, `PV_LIB_SPEC_F166Full, `PV_LIB_SPEC_F166Whole, `PV_LIB_SPEC_F170Full, `PV_LIB_SPEC_F170PackageComparison, `PV_LIB_SPEC_F170PackagePair]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_DisjointPre18.n_typed, `PV_LIB_SPEC_DisjointPre18.owner, `PV_LIB_SPEC_DisjointPre18.pre, `PV_LIB_SPEC_DisjointPre18.receivers, `PV_LIB_SPEC_DisjointPre18.run_bytes, `PV_LIB_SPEC_DisjointPre18.run_typed, `PV_LIB_SPEC_DisjointPre18.tasks_typed, `PV_LIB_SPEC_DisjointPre18.validity, `PV_LIB_SPEC_Entry13.active, `PV_LIB_SPEC_Entry13.input, `PV_LIB_SPEC_Entry13.native_thread, `PV_LIB_SPEC_Entry13.slot, `PV_LIB_SPEC_Entry13.source_active, `PV_LIB_SPEC_Entry13.state, `PV_LIB_SPEC_Entry13.store, `PV_LIB_SPEC_Entry14.hooksSlot, `PV_LIB_SPEC_Entry14.input, `PV_LIB_SPEC_Entry14.memory_before, `PV_LIB_SPEC_Entry14.state, `PV_LIB_SPEC_EntryPre13.captured, `PV_LIB_SPEC_EntryPre13.f_typed, `PV_LIB_SPEC_EntryPre13.memory_before, `PV_LIB_SPEC_EntryPre13.n_bytes, `PV_LIB_SPEC_EntryPre13.n_typed, `PV_LIB_SPEC_EntryPre13.owner, `PV_LIB_SPEC_EntryPre13.pre, `PV_LIB_SPEC_EntryPre13.receivers, `PV_LIB_SPEC_EntryPre13.run_bytes, `PV_LIB_SPEC_EntryPre13.run_typed, `PV_LIB_SPEC_EntryPre13.tasks_typed, `PV_LIB_SPEC_EntryPre14.captured, `PV_LIB_SPEC_EntryPre14.f_typed, `PV_LIB_SPEC_EntryPre14.memory_before, `PV_LIB_SPEC_EntryPre14.n_bytes, `PV_LIB_SPEC_EntryPre14.n_typed, `PV_LIB_SPEC_EntryPre14.owner, `PV_LIB_SPEC_EntryPre14.pre, `PV_LIB_SPEC_EntryPre14.receivers, `PV_LIB_SPEC_EntryPre14.run_bytes, `PV_LIB_SPEC_EntryPre14.run_typed, `PV_LIB_SPEC_EntryPre14.tasks_typed, `PV_LIB_SPEC_EntryWorld18.Entry, `PV_LIB_SPEC_EntryWorld18.StackGrant, `PV_LIB_SPEC_EntryWorld18.concrete, `PV_LIB_SPEC_EntryWorld18.concrete_pre, `PV_LIB_SPEC_EntryWorld18.concrete_pre_data, `PV_LIB_SPEC_EntryWorld18.frame, `PV_LIB_SPEC_EntryWorld18.inhabited, `PV_LIB_SPEC_EntryWorld18.input, `PV_LIB_SPEC_EntryWorld18.paired, `PV_LIB_SPEC_EntryWorld18.stack_contains, `PV_LIB_SPEC_Environment.Channel, `PV_LIB_SPEC_Environment.Env, `PV_LIB_SPEC_Environment.Law, `PV_LIB_SPEC_Environment.ObservedLaw, `PV_LIB_SPEC_Environment.Request, `PV_LIB_SPEC_Environment.Site, `PV_LIB_SPEC_Environment.abort_prefix, `PV_LIB_SPEC_Environment.functional, `PV_LIB_SPEC_Environment.nonempty, `PV_LIB_SPEC_Environment.observe, `PV_LIB_SPEC_Environment.observed_functional, `PV_LIB_SPEC_Environment.pendingEnv, `PV_LIB_SPEC_Environment.reply]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_F0Full.Captures, `PV_LIB_SPEC_F0Full.Comparison, `PV_LIB_SPEC_F0Full.Contract, `PV_LIB_SPEC_F0Full.Input, `PV_LIB_SPEC_F0Full.MachineSpec, `PV_LIB_SPEC_F0Full.Original, `PV_LIB_SPEC_F0Full.PackageStatement, `PV_LIB_SPEC_F0Full.Post, `PV_LIB_SPEC_F0Full.PostRoot, `PV_LIB_SPEC_F0Full.Pre, `PV_LIB_SPEC_F0Full.PreRoot, `PV_LIB_SPEC_F0Full.RootFrame, `PV_LIB_SPEC_F0Full.referenceInput, `PV_LIB_SPEC_F0Full.rootEntry, `PV_LIB_SPEC_F125Full.Comparison, `PV_LIB_SPEC_F125Full.Contract, `PV_LIB_SPEC_F125Full.Input, `PV_LIB_SPEC_F125Full.MachineSpec, `PV_LIB_SPEC_F125Full.PackageStatement, `PV_LIB_SPEC_F125Full.Post, `PV_LIB_SPEC_F125Full.Pre, `PV_LIB_SPEC_F15Full.Comparison, `PV_LIB_SPEC_F15Full.Contract, `PV_LIB_SPEC_F15Full.Input, `PV_LIB_SPEC_F15Full.MachineSpec, `PV_LIB_SPEC_F15Full.PackageStatement, `PV_LIB_SPEC_F15Full.Post, `PV_LIB_SPEC_F15Full.Pre, `PV_LIB_SPEC_F15Whole.Comparison, `PV_LIB_SPEC_F15Whole.Contract, `PV_LIB_SPEC_F15Whole.Input, `PV_LIB_SPEC_F15Whole.MachineSpec, `PV_LIB_SPEC_F15Whole.PackageStatement, `PV_LIB_SPEC_F15Whole.Post, `PV_LIB_SPEC_F15Whole.Pre, `PV_LIB_SPEC_F166Full.Comparison, `PV_LIB_SPEC_F166Full.Contract, `PV_LIB_SPEC_F166Full.Input, `PV_LIB_SPEC_F166Full.MachineSpec, `PV_LIB_SPEC_F166Full.PackageStatement, `PV_LIB_SPEC_F166Full.Post, `PV_LIB_SPEC_F166Full.Pre, `PV_LIB_SPEC_F166Whole.Comparison, `PV_LIB_SPEC_F166Whole.Contract, `PV_LIB_SPEC_F166Whole.Input, `PV_LIB_SPEC_F166Whole.MachineSpec, `PV_LIB_SPEC_F166Whole.PackageStatement, `PV_LIB_SPEC_F166Whole.Post, `PV_LIB_SPEC_F166Whole.Pre, `PV_LIB_SPEC_F170Full.Comparison, `PV_LIB_SPEC_F170Full.Contract, `PV_LIB_SPEC_F170Full.Input, `PV_LIB_SPEC_F170Full.MachineSpec, `PV_LIB_SPEC_F170Full.Post, `PV_LIB_SPEC_F170Full.Pre, `PV_LIB_SPEC_F170PackageComparison.Comparison, `PV_LIB_SPEC_F170PackageComparison.PackageContract, `PV_LIB_SPEC_F170PackageComparison.PackageMachineSpec, `PV_LIB_SPEC_F170PackageComparison.PackagePost, `PV_LIB_SPEC_F170PackageComparison.PackagePre, `PV_LIB_SPEC_F170PackagePair.Comparison]
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
