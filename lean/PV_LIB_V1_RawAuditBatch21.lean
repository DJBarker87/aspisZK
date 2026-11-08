import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_F361ArcMachineGap, `PV_LIB_SPEC_F361Contract, `PV_LIB_SPEC_F361Entry, `PV_LIB_SPEC_F361Full, `PV_LIB_SPEC_F361Whole, `PV_LIB_SPEC_F5Full, `PV_LIB_SPEC_F5PackageComparison, `PV_LIB_SPEC_F6Full, `PV_LIB_SPEC_FixedNativeGap17, `PV_LIB_SPEC_OwnInitFull, `PV_LIB_SPEC_ThreadSpecifications]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_F361ArcMachineGap.State, `PV_LIB_SPEC_F361ArcMachineGap.before, `PV_LIB_SPEC_F361ArcMachineGap.count_unchanged, `PV_LIB_SPEC_F361ArcMachineGap.increment_impossible, `PV_LIB_SPEC_F361ArcMachineGap.native_poll, `PV_LIB_SPEC_F361Contract.PackageTransport, `PV_LIB_SPEC_F361Contract.Post, `PV_LIB_SPEC_F361Contract.Pre, `PV_LIB_SPEC_F361Contract.RegisteredValidity, `PV_LIB_SPEC_F361Contract.SourceAdequacy, `PV_LIB_SPEC_F361Contract.implies_package, `PV_LIB_SPEC_F361Contract.machine, `PV_LIB_SPEC_F361Contract.pre_comparison, `PV_LIB_SPEC_F361Contract.reference, `PV_LIB_SPEC_F361Contract.registration, `PV_LIB_SPEC_F361Entry.EntryComponent, `PV_LIB_SPEC_F361Entry.Numbered, `PV_LIB_SPEC_F361Entry.PackagePost, `PV_LIB_SPEC_F361Entry.PackagePre, `PV_LIB_SPEC_F361Entry.Representation, `PV_LIB_SPEC_F361Entry.before_after, `PV_LIB_SPEC_F361Entry.implies_name, `PV_LIB_SPEC_F361Entry.implies_package, `PV_LIB_SPEC_F361Entry.implies_scope, `PV_LIB_SPEC_F361Entry.post_literal, `PV_LIB_SPEC_F361Full.Comparison, `PV_LIB_SPEC_F361Full.Contract, `PV_LIB_SPEC_F361Full.Input, `PV_LIB_SPEC_F361Full.MachineSpec, `PV_LIB_SPEC_F361Full.PackagePost, `PV_LIB_SPEC_F361Full.PackagePre, `PV_LIB_SPEC_F361Full.Post, `PV_LIB_SPEC_F361Full.Pre, `PV_LIB_SPEC_F361Full.Representation, `PV_LIB_SPEC_F361Full.runtime, `PV_LIB_SPEC_F361Full.source, `PV_LIB_SPEC_F361Whole.Comparison, `PV_LIB_SPEC_F361Whole.Contract, `PV_LIB_SPEC_F361Whole.MachineSpec, `PV_LIB_SPEC_F361Whole.Post, `PV_LIB_SPEC_F361Whole.Pre, `PV_LIB_SPEC_F361Whole.Representation, `PV_LIB_SPEC_F361Whole.SourceAdequacy, `PV_LIB_SPEC_F361Whole.State, `PV_LIB_SPEC_F361Whole.source, `PV_LIB_SPEC_F5Full.Comparison, `PV_LIB_SPEC_F5Full.Contract, `PV_LIB_SPEC_F5Full.Input, `PV_LIB_SPEC_F5Full.MachineSpec, `PV_LIB_SPEC_F5Full.Post, `PV_LIB_SPEC_F5Full.Pre, `PV_LIB_SPEC_F5PackageComparison.Comparison, `PV_LIB_SPEC_F5PackageComparison.PackageContract, `PV_LIB_SPEC_F5PackageComparison.PackageMachineSpec, `PV_LIB_SPEC_F5PackageComparison.PackagePost, `PV_LIB_SPEC_F5PackageComparison.PackagePre, `PV_LIB_SPEC_F6Full.Comparison, `PV_LIB_SPEC_F6Full.Contract, `PV_LIB_SPEC_F6Full.Input, `PV_LIB_SPEC_F6Full.MachineSpec, `PV_LIB_SPEC_F6Full.PackageContract, `PV_LIB_SPEC_F6Full.PackagePost, `PV_LIB_SPEC_F6Full.PackagePre, `PV_LIB_SPEC_F6Full.Post]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_F6Full.Pre, `PV_LIB_SPEC_F6Full.packageInput, `PV_LIB_SPEC_FixedNativeGap17.bound_answer, `PV_LIB_SPEC_FixedNativeGap17.fixed_answer, `PV_LIB_SPEC_FixedNativeGap17.no_reply_identity, `PV_LIB_SPEC_Frontier.Aborts, `PV_LIB_SPEC_Frontier.Behavior, `PV_LIB_SPEC_Frontier.Boundary, `PV_LIB_SPEC_Frontier.Comparison, `PV_LIB_SPEC_Frontier.First, `PV_LIB_SPEC_Frontier.Pending, `PV_LIB_SPEC_Frontier.Post, `PV_LIB_SPEC_Frontier.observe, `PV_LIB_SPEC_Frozen.EntryComparison, `PV_LIB_SPEC_Frozen.EntryPre, `PV_LIB_SPEC_Frozen.Environment, `PV_LIB_SPEC_Frozen.F0.Comparison, `PV_LIB_SPEC_Frozen.F0.Contract, `PV_LIB_SPEC_Frozen.F0.Input, `PV_LIB_SPEC_Frozen.F0.MachineSpec, `PV_LIB_SPEC_Frozen.F0.Original, `PV_LIB_SPEC_Frozen.F0.Post, `PV_LIB_SPEC_Frozen.F0.PostRoot, `PV_LIB_SPEC_Frozen.F0.Pre, `PV_LIB_SPEC_Frozen.F0.PreRoot, `PV_LIB_SPEC_Frozen.F1.Comparison, `PV_LIB_SPEC_Frozen.F1.Contract, `PV_LIB_SPEC_Frozen.F1.Input, `PV_LIB_SPEC_Frozen.F1.MachineSpec, `PV_LIB_SPEC_Frozen.F1.Post, `PV_LIB_SPEC_Frozen.F1.Pre, `PV_LIB_SPEC_Frozen.F125.Comparison, `PV_LIB_SPEC_Frozen.F125.Contract, `PV_LIB_SPEC_Frozen.F125.Input, `PV_LIB_SPEC_Frozen.F125.MachineSpec, `PV_LIB_SPEC_Frozen.F125.Post, `PV_LIB_SPEC_Frozen.F125.Pre, `PV_LIB_SPEC_Frozen.F15.Comparison, `PV_LIB_SPEC_Frozen.F15.Contract, `PV_LIB_SPEC_Frozen.F15.Input, `PV_LIB_SPEC_Frozen.F15.MachineSpec, `PV_LIB_SPEC_Frozen.F15.Post, `PV_LIB_SPEC_Frozen.F15.Pre, `PV_LIB_SPEC_Frozen.F166.Comparison, `PV_LIB_SPEC_Frozen.F166.Contract, `PV_LIB_SPEC_Frozen.F166.Input, `PV_LIB_SPEC_Frozen.F166.MachineSpec, `PV_LIB_SPEC_Frozen.F166.Post, `PV_LIB_SPEC_Frozen.F166.Pre, `PV_LIB_SPEC_Frozen.F17.Comparison, `PV_LIB_SPEC_Frozen.F17.Contract, `PV_LIB_SPEC_Frozen.F17.Input, `PV_LIB_SPEC_Frozen.F17.MachineSpec, `PV_LIB_SPEC_Frozen.F17.Post, `PV_LIB_SPEC_Frozen.F17.Pre, `PV_LIB_SPEC_Frozen.F170.Comparison, `PV_LIB_SPEC_Frozen.F170.Contract, `PV_LIB_SPEC_Frozen.F170.Input, `PV_LIB_SPEC_Frozen.F170.MachineSpec, `PV_LIB_SPEC_Frozen.F170.Post, `PV_LIB_SPEC_Frozen.F170.Pre]
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
