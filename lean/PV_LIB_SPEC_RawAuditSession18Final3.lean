import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_NativeTargets18, `PV_LIB_SPEC_ContextReply18, `PV_LIB_SPEC_NativeContext18, `PV_LIB_SPEC_ContextCounter18, `PV_LIB_SPEC_ContextCounterPost18, `PV_LIB_SPEC_ContextFinalF36118, `PV_LIB_SPEC_ContextFinalF27018, `PV_LIB_SPEC_ContextFinalF16618, `PV_LIB_SPEC_ContextFinalF1518, `PV_LIB_SPEC_ContextFinalF20818, `PV_LIB_SPEC_ContextFinalF22018, `PV_LIB_SPEC_ContextFinalF31618, `PV_LIB_SPEC_ContextFinalF31818, `PV_LIB_SPEC_ContextFinalF21918, `PV_LIB_SPEC_ContextFinalF12518, `PV_LIB_SPEC_ContextFinalF618, `PV_LIB_SPEC_ContextFinalF17018, `PV_LIB_SPEC_ContextFinalF1718, `PV_LIB_SPEC_ContextFinalF518, `PV_LIB_SPEC_ContextFinalF218, `PV_LIB_SPEC_ContextFinalF118, `PV_LIB_SPEC_ContextFinalF018, `PV_LIB_SPEC_ContextFinalOwnInit18, `PV_LIB_SPEC_ContextFinalContracts18],
     #[`PV_LIB_SPEC_NativeTargets18.ActiveBeforeF6, `PV_LIB_SPEC_NativeTargets18.StackSize, `PV_LIB_SPEC_NativeTargets18.Hooks, `PV_LIB_SPEC_ContextReply18.fixed_answer, `PV_LIB_SPEC_ContextReply18.bound_answer, `PV_LIB_SPEC_ContextReply18.no_reply_identity, `PV_LIB_SPEC_ContextReply18.history_same, `PV_LIB_SPEC_ContextReply18.delivery84, `PV_LIB_SPEC_NativeContext18.shape, `PV_LIB_SPEC_NativeContext18.bound, `PV_LIB_SPEC_NativeContext18.prefix_wait, `PV_LIB_SPEC_ContextCounter18.Observation, `PV_LIB_SPEC_ContextCounter18.observe, `PV_LIB_SPEC_ContextCounter18.Behavior, `PV_LIB_SPEC_ContextCounter18.sample, `PV_LIB_SPEC_ContextCounter18.old_distinguishes, `PV_LIB_SPEC_ContextCounter18.counter_abstracted, `PV_LIB_SPEC_ContextCounter18.source_cells, `PV_LIB_SPEC_ContextCounter18.sample_histories_ignored, `PV_LIB_SPEC_ContextCounter18.sample_numbered, `PV_LIB_SPEC_ContextCounter18.sample_owner, `PV_LIB_SPEC_ContextCounterPost18.Post, `PV_LIB_SPEC_ContextCounterPost18.ordinary, `PV_LIB_SPEC_ContextFinalF36118.Input, `PV_LIB_SPEC_ContextFinalF36118.Representation, `PV_LIB_SPEC_ContextFinalF36118.Pre, `PV_LIB_SPEC_ContextFinalF36118.MachineSpec, `PV_LIB_SPEC_ContextFinalF36118.Post, `PV_LIB_SPEC_ContextFinalF36118.Contract, `PV_LIB_SPEC_ContextFinalF36118.pre_same, `PV_LIB_SPEC_ContextFinalF36118.Before, `PV_LIB_SPEC_ContextFinalF36118.CounterBefore, `PV_LIB_SPEC_ContextFinalF27018.Input, `PV_LIB_SPEC_ContextFinalF27018.Pre, `PV_LIB_SPEC_ContextFinalF27018.MachineSpec, `PV_LIB_SPEC_ContextFinalF27018.Before, `PV_LIB_SPEC_ContextFinalF27018.CounterBefore, `PV_LIB_SPEC_ContextFinalF27018.Post, `PV_LIB_SPEC_ContextFinalF27018.Contract, `PV_LIB_SPEC_ContextFinalF27018.pre_same, `PV_LIB_SPEC_ContextFinalF16618.Input, `PV_LIB_SPEC_ContextFinalF16618.Pre, `PV_LIB_SPEC_ContextFinalF16618.MachineSpec, `PV_LIB_SPEC_ContextFinalF16618.Before, `PV_LIB_SPEC_ContextFinalF16618.CounterBefore, `PV_LIB_SPEC_ContextFinalF16618.Post, `PV_LIB_SPEC_ContextFinalF16618.Contract, `PV_LIB_SPEC_ContextFinalF16618.pre_same, `PV_LIB_SPEC_ContextFinalF1518.Input, `PV_LIB_SPEC_ContextFinalF1518.Pre, `PV_LIB_SPEC_ContextFinalF1518.MachineSpec, `PV_LIB_SPEC_ContextFinalF1518.Before, `PV_LIB_SPEC_ContextFinalF1518.CounterBefore, `PV_LIB_SPEC_ContextFinalF1518.Post, `PV_LIB_SPEC_ContextFinalF1518.Contract, `PV_LIB_SPEC_ContextFinalF1518.pre_same, `PV_LIB_SPEC_ContextFinalF20818.Input, `PV_LIB_SPEC_ContextFinalF20818.Pre, `PV_LIB_SPEC_ContextFinalF20818.MachineSpec, `PV_LIB_SPEC_ContextFinalF20818.Before, `PV_LIB_SPEC_ContextFinalF20818.CounterBefore, `PV_LIB_SPEC_ContextFinalF20818.Post, `PV_LIB_SPEC_ContextFinalF20818.Contract, `PV_LIB_SPEC_ContextFinalF20818.pre_same, `PV_LIB_SPEC_ContextFinalF22018.Input, `PV_LIB_SPEC_ContextFinalF22018.Pre, `PV_LIB_SPEC_ContextFinalF22018.MachineSpec, `PV_LIB_SPEC_ContextFinalF22018.Before, `PV_LIB_SPEC_ContextFinalF22018.CounterBefore, `PV_LIB_SPEC_ContextFinalF22018.Post, `PV_LIB_SPEC_ContextFinalF22018.Contract, `PV_LIB_SPEC_ContextFinalF22018.pre_same, `PV_LIB_SPEC_ContextFinalF31618.Input, `PV_LIB_SPEC_ContextFinalF31618.Pre, `PV_LIB_SPEC_ContextFinalF31618.MachineSpec, `PV_LIB_SPEC_ContextFinalF31618.Before, `PV_LIB_SPEC_ContextFinalF31618.CounterBefore, `PV_LIB_SPEC_ContextFinalF31618.Post, `PV_LIB_SPEC_ContextFinalF31618.Contract, `PV_LIB_SPEC_ContextFinalF31618.pre_same, `PV_LIB_SPEC_ContextFinalF31818.Input, `PV_LIB_SPEC_ContextFinalF31818.Pre, `PV_LIB_SPEC_ContextFinalF31818.MachineSpec, `PV_LIB_SPEC_ContextFinalF31818.Before, `PV_LIB_SPEC_ContextFinalF31818.CounterBefore, `PV_LIB_SPEC_ContextFinalF31818.Post, `PV_LIB_SPEC_ContextFinalF31818.Contract, `PV_LIB_SPEC_ContextFinalF31818.pre_same, `PV_LIB_SPEC_ContextFinalF21918.Input, `PV_LIB_SPEC_ContextFinalF21918.Pre, `PV_LIB_SPEC_ContextFinalF21918.MachineSpec, `PV_LIB_SPEC_ContextFinalF21918.Before, `PV_LIB_SPEC_ContextFinalF21918.CounterBefore, `PV_LIB_SPEC_ContextFinalF21918.Post, `PV_LIB_SPEC_ContextFinalF21918.Contract, `PV_LIB_SPEC_ContextFinalF21918.pre_same, `PV_LIB_SPEC_ContextFinalF12518.Input, `PV_LIB_SPEC_ContextFinalF12518.Pre, `PV_LIB_SPEC_ContextFinalF12518.MachineSpec, `PV_LIB_SPEC_ContextFinalF12518.Before, `PV_LIB_SPEC_ContextFinalF12518.CounterBefore, `PV_LIB_SPEC_ContextFinalF12518.Post, `PV_LIB_SPEC_ContextFinalF12518.Contract, `PV_LIB_SPEC_ContextFinalF12518.pre_same, `PV_LIB_SPEC_ContextFinalF618.Input, `PV_LIB_SPEC_ContextFinalF618.Pre, `PV_LIB_SPEC_ContextFinalF618.MachineSpec, `PV_LIB_SPEC_ContextFinalF618.Before, `PV_LIB_SPEC_ContextFinalF618.CounterBefore, `PV_LIB_SPEC_ContextFinalF618.Post, `PV_LIB_SPEC_ContextFinalF618.Contract, `PV_LIB_SPEC_ContextFinalF618.pre_same, `PV_LIB_SPEC_ContextFinalF17018.Input, `PV_LIB_SPEC_ContextFinalF17018.Pre, `PV_LIB_SPEC_ContextFinalF17018.MachineSpec, `PV_LIB_SPEC_ContextFinalF17018.Before, `PV_LIB_SPEC_ContextFinalF17018.CounterBefore, `PV_LIB_SPEC_ContextFinalF17018.Post, `PV_LIB_SPEC_ContextFinalF17018.Contract, `PV_LIB_SPEC_ContextFinalF17018.pre_same, `PV_LIB_SPEC_ContextFinalF1718.Input, `PV_LIB_SPEC_ContextFinalF1718.Pre, `PV_LIB_SPEC_ContextFinalF1718.MachineSpec, `PV_LIB_SPEC_ContextFinalF1718.Before, `PV_LIB_SPEC_ContextFinalF1718.CounterBefore, `PV_LIB_SPEC_ContextFinalF1718.Post, `PV_LIB_SPEC_ContextFinalF1718.Contract, `PV_LIB_SPEC_ContextFinalF1718.pre_same, `PV_LIB_SPEC_ContextFinalF518.Input, `PV_LIB_SPEC_ContextFinalF518.Pre, `PV_LIB_SPEC_ContextFinalF518.MachineSpec, `PV_LIB_SPEC_ContextFinalF518.Before, `PV_LIB_SPEC_ContextFinalF518.CounterBefore, `PV_LIB_SPEC_ContextFinalF518.Post, `PV_LIB_SPEC_ContextFinalF518.Contract, `PV_LIB_SPEC_ContextFinalF518.pre_same, `PV_LIB_SPEC_ContextFinalF218.Input, `PV_LIB_SPEC_ContextFinalF218.Pre, `PV_LIB_SPEC_ContextFinalF218.MachineSpec, `PV_LIB_SPEC_ContextFinalF218.Before, `PV_LIB_SPEC_ContextFinalF218.CounterBefore, `PV_LIB_SPEC_ContextFinalF218.Post, `PV_LIB_SPEC_ContextFinalF218.Contract, `PV_LIB_SPEC_ContextFinalF218.pre_same, `PV_LIB_SPEC_ContextFinalF118.Input, `PV_LIB_SPEC_ContextFinalF118.Pre, `PV_LIB_SPEC_ContextFinalF118.MachineSpec, `PV_LIB_SPEC_ContextFinalF118.Before, `PV_LIB_SPEC_ContextFinalF118.CounterBefore, `PV_LIB_SPEC_ContextFinalF118.Post, `PV_LIB_SPEC_ContextFinalF118.Contract, `PV_LIB_SPEC_ContextFinalF118.pre_same, `PV_LIB_SPEC_ContextFinalF018.Input, `PV_LIB_SPEC_ContextFinalF018.Pre, `PV_LIB_SPEC_ContextFinalF018.MachineSpec, `PV_LIB_SPEC_ContextFinalF018.Before, `PV_LIB_SPEC_ContextFinalF018.CounterBefore, `PV_LIB_SPEC_ContextFinalF018.PostRoot, `PV_LIB_SPEC_ContextFinalF018.Post, `PV_LIB_SPEC_ContextFinalF018.Contract, `PV_LIB_SPEC_ContextFinalF018.pre_same, `PV_LIB_SPEC_ContextFinalOwnInit18.Input, `PV_LIB_SPEC_ContextFinalOwnInit18.Pre, `PV_LIB_SPEC_ContextFinalOwnInit18.Representation, `PV_LIB_SPEC_ContextFinalOwnInit18.MachineSpec, `PV_LIB_SPEC_ContextFinalOwnInit18.Before, `PV_LIB_SPEC_ContextFinalOwnInit18.CounterBefore, `PV_LIB_SPEC_ContextFinalOwnInit18.Boundary, `PV_LIB_SPEC_ContextFinalOwnInit18.First, `PV_LIB_SPEC_ContextFinalOwnInit18.Post, `PV_LIB_SPEC_ContextFinalOwnInit18.Contract, `PV_LIB_SPEC_ContextFinalOwnInit18.pre_same, `PV_LIB_SPEC_ContextFinalContracts18.Implementations, `PV_LIB_SPEC_ContextFinalContracts18.Contracts, `PV_LIB_SPEC_ContextFinalContracts18.Before, `PV_LIB_SPEC_ContextFinalContracts18.CounterBefore])
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
