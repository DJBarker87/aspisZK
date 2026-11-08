import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_ContextF16618, `PV_LIB_SPEC_ContextF17018, `PV_LIB_SPEC_ContextF1718, `PV_LIB_SPEC_ContextF20818, `PV_LIB_SPEC_ContextF218, `PV_LIB_SPEC_ContextF21918, `PV_LIB_SPEC_ContextF22018, `PV_LIB_SPEC_ContextF27018, `PV_LIB_SPEC_ContextF31618, `PV_LIB_SPEC_ContextF31818, `PV_LIB_SPEC_ContextF36118, `PV_LIB_SPEC_ContextF518, `PV_LIB_SPEC_ContextF618, `PV_LIB_SPEC_ContextFinalContracts18, `PV_LIB_SPEC_ContextFinalF018, `PV_LIB_SPEC_ContextFinalF118, `PV_LIB_SPEC_ContextFinalF12518, `PV_LIB_SPEC_ContextFinalF1518, `PV_LIB_SPEC_ContextFinalF16618]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_ContextF16618.Pre, `PV_LIB_SPEC_ContextF16618.pre_same, `PV_LIB_SPEC_ContextF17018.Before, `PV_LIB_SPEC_ContextF17018.Contract, `PV_LIB_SPEC_ContextF17018.Input, `PV_LIB_SPEC_ContextF17018.MachineSpec, `PV_LIB_SPEC_ContextF17018.Post, `PV_LIB_SPEC_ContextF17018.Pre, `PV_LIB_SPEC_ContextF17018.pre_same, `PV_LIB_SPEC_ContextF1718.Before, `PV_LIB_SPEC_ContextF1718.Contract, `PV_LIB_SPEC_ContextF1718.Input, `PV_LIB_SPEC_ContextF1718.MachineSpec, `PV_LIB_SPEC_ContextF1718.Post, `PV_LIB_SPEC_ContextF1718.Pre, `PV_LIB_SPEC_ContextF1718.pre_same, `PV_LIB_SPEC_ContextF20818.Before, `PV_LIB_SPEC_ContextF20818.Contract, `PV_LIB_SPEC_ContextF20818.Input, `PV_LIB_SPEC_ContextF20818.MachineSpec, `PV_LIB_SPEC_ContextF20818.Post, `PV_LIB_SPEC_ContextF20818.Pre, `PV_LIB_SPEC_ContextF20818.pre_same, `PV_LIB_SPEC_ContextF218.Before, `PV_LIB_SPEC_ContextF218.Contract, `PV_LIB_SPEC_ContextF218.Input, `PV_LIB_SPEC_ContextF218.MachineSpec, `PV_LIB_SPEC_ContextF218.Post, `PV_LIB_SPEC_ContextF218.Pre, `PV_LIB_SPEC_ContextF218.pre_same, `PV_LIB_SPEC_ContextF21918.Before, `PV_LIB_SPEC_ContextF21918.Contract, `PV_LIB_SPEC_ContextF21918.Input, `PV_LIB_SPEC_ContextF21918.MachineSpec, `PV_LIB_SPEC_ContextF21918.Post, `PV_LIB_SPEC_ContextF21918.Pre, `PV_LIB_SPEC_ContextF21918.pre_same, `PV_LIB_SPEC_ContextF22018.Before, `PV_LIB_SPEC_ContextF22018.Contract, `PV_LIB_SPEC_ContextF22018.Input, `PV_LIB_SPEC_ContextF22018.MachineSpec, `PV_LIB_SPEC_ContextF22018.Post, `PV_LIB_SPEC_ContextF22018.Pre, `PV_LIB_SPEC_ContextF22018.pre_same, `PV_LIB_SPEC_ContextF27018.Before, `PV_LIB_SPEC_ContextF27018.Contract, `PV_LIB_SPEC_ContextF27018.Input, `PV_LIB_SPEC_ContextF27018.MachineSpec, `PV_LIB_SPEC_ContextF27018.Post, `PV_LIB_SPEC_ContextF27018.Pre, `PV_LIB_SPEC_ContextF27018.pre_same, `PV_LIB_SPEC_ContextF31618.Before, `PV_LIB_SPEC_ContextF31618.Contract, `PV_LIB_SPEC_ContextF31618.Input, `PV_LIB_SPEC_ContextF31618.MachineSpec, `PV_LIB_SPEC_ContextF31618.Post, `PV_LIB_SPEC_ContextF31618.Pre, `PV_LIB_SPEC_ContextF31618.pre_same, `PV_LIB_SPEC_ContextF31818.Before, `PV_LIB_SPEC_ContextF31818.Contract, `PV_LIB_SPEC_ContextF31818.Input, `PV_LIB_SPEC_ContextF31818.MachineSpec, `PV_LIB_SPEC_ContextF31818.Post, `PV_LIB_SPEC_ContextF31818.Pre]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_ContextF31818.pre_same, `PV_LIB_SPEC_ContextF36118.Before, `PV_LIB_SPEC_ContextF36118.Contract, `PV_LIB_SPEC_ContextF36118.Input, `PV_LIB_SPEC_ContextF36118.MachineSpec, `PV_LIB_SPEC_ContextF36118.Post, `PV_LIB_SPEC_ContextF36118.Pre, `PV_LIB_SPEC_ContextF36118.Representation, `PV_LIB_SPEC_ContextF36118.pre_same, `PV_LIB_SPEC_ContextF518.Before, `PV_LIB_SPEC_ContextF518.Contract, `PV_LIB_SPEC_ContextF518.Input, `PV_LIB_SPEC_ContextF518.MachineSpec, `PV_LIB_SPEC_ContextF518.Post, `PV_LIB_SPEC_ContextF518.Pre, `PV_LIB_SPEC_ContextF518.pre_same, `PV_LIB_SPEC_ContextF618.Before, `PV_LIB_SPEC_ContextF618.Contract, `PV_LIB_SPEC_ContextF618.Input, `PV_LIB_SPEC_ContextF618.MachineSpec, `PV_LIB_SPEC_ContextF618.Post, `PV_LIB_SPEC_ContextF618.Pre, `PV_LIB_SPEC_ContextF618.pre_same, `PV_LIB_SPEC_ContextFinalContracts18.Before, `PV_LIB_SPEC_ContextFinalContracts18.Contracts, `PV_LIB_SPEC_ContextFinalContracts18.CounterBefore, `PV_LIB_SPEC_ContextFinalContracts18.Implementations, `PV_LIB_SPEC_ContextFinalF018.Before, `PV_LIB_SPEC_ContextFinalF018.Contract, `PV_LIB_SPEC_ContextFinalF018.CounterBefore, `PV_LIB_SPEC_ContextFinalF018.Input, `PV_LIB_SPEC_ContextFinalF018.MachineSpec, `PV_LIB_SPEC_ContextFinalF018.Post, `PV_LIB_SPEC_ContextFinalF018.PostRoot, `PV_LIB_SPEC_ContextFinalF018.Pre, `PV_LIB_SPEC_ContextFinalF018.pre_same, `PV_LIB_SPEC_ContextFinalF118.Before, `PV_LIB_SPEC_ContextFinalF118.Contract, `PV_LIB_SPEC_ContextFinalF118.CounterBefore, `PV_LIB_SPEC_ContextFinalF118.Input, `PV_LIB_SPEC_ContextFinalF118.MachineSpec, `PV_LIB_SPEC_ContextFinalF118.Post, `PV_LIB_SPEC_ContextFinalF118.Pre, `PV_LIB_SPEC_ContextFinalF118.pre_same, `PV_LIB_SPEC_ContextFinalF12518.Before, `PV_LIB_SPEC_ContextFinalF12518.Contract, `PV_LIB_SPEC_ContextFinalF12518.CounterBefore, `PV_LIB_SPEC_ContextFinalF12518.Input, `PV_LIB_SPEC_ContextFinalF12518.MachineSpec, `PV_LIB_SPEC_ContextFinalF12518.Post, `PV_LIB_SPEC_ContextFinalF12518.Pre, `PV_LIB_SPEC_ContextFinalF12518.pre_same, `PV_LIB_SPEC_ContextFinalF1518.Before, `PV_LIB_SPEC_ContextFinalF1518.Contract, `PV_LIB_SPEC_ContextFinalF1518.CounterBefore, `PV_LIB_SPEC_ContextFinalF1518.Input, `PV_LIB_SPEC_ContextFinalF1518.MachineSpec, `PV_LIB_SPEC_ContextFinalF1518.Post, `PV_LIB_SPEC_ContextFinalF1518.Pre, `PV_LIB_SPEC_ContextFinalF1518.pre_same, `PV_LIB_SPEC_ContextFinalF16618.Before]
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
