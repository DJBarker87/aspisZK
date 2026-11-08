import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_ThreadContract, `PV_LIB_SPEC_F361Contract, `PV_LIB_SPEC_OwnInitEntry],
     #[`PV_LIB_SPEC_ThreadContract.storeView, `PV_LIB_SPEC_ThreadContract.configView, `PV_LIB_SPEC_ThreadContract.statusView, `PV_LIB_SPEC_ThreadContract.Observation, `PV_LIB_SPEC_ThreadContract.observe, `PV_LIB_SPEC_ThreadContract.Numbered, `PV_LIB_SPEC_ThreadContract.OwnComplete, `PV_LIB_SPEC_ThreadContract.Terminal, `PV_LIB_SPEC_ThreadContract.ConsumedPending, `PV_LIB_SPEC_ThreadContract.Boundary, `PV_LIB_SPEC_ThreadContract.First, `PV_LIB_SPEC_ThreadContract.Diverges, `PV_LIB_SPEC_ThreadContract.reference, `PV_LIB_SPEC_ThreadContract.BehavioralPost, `PV_LIB_SPEC_ThreadContract.SourceAdequacy, `PV_LIB_SPEC_ThreadContract.abort_prefix, `PV_LIB_SPEC_ThreadContract.counter_irrelevant, `PV_LIB_SPEC_F361Contract.machine, `PV_LIB_SPEC_F361Contract.RegisteredValidity, `PV_LIB_SPEC_F361Contract.Pre, `PV_LIB_SPEC_F361Contract.reference, `PV_LIB_SPEC_F361Contract.Post, `PV_LIB_SPEC_F361Contract.PackageTransport, `PV_LIB_SPEC_F361Contract.SourceAdequacy, `PV_LIB_SPEC_F361Contract.pre_comparison, `PV_LIB_SPEC_F361Contract.implies_package, `PV_LIB_SPEC_F361Contract.registration, `PV_LIB_SPEC_OwnInitEntry.site, `PV_LIB_SPEC_OwnInitEntry.zero, `PV_LIB_SPEC_OwnInitEntry.captures, `PV_LIB_SPEC_OwnInitEntry.places, `PV_LIB_SPEC_OwnInitEntry.runHeader, `PV_LIB_SPEC_OwnInitEntry.nHeader, `PV_LIB_SPEC_OwnInitEntry.fHeader, `PV_LIB_SPEC_OwnInitEntry.taskHeader, `PV_LIB_SPEC_OwnInitEntry.bytes, `PV_LIB_SPEC_OwnInitEntry.state, `PV_LIB_SPEC_OwnInitEntry.receivers, `PV_LIB_SPEC_OwnInitEntry.run_bytes, `PV_LIB_SPEC_OwnInitEntry.n_bytes, `PV_LIB_SPEC_OwnInitEntry.run_typed, `PV_LIB_SPEC_OwnInitEntry.n_typed, `PV_LIB_SPEC_OwnInitEntry.f_typed, `PV_LIB_SPEC_OwnInitEntry.tasks_typed, `PV_LIB_SPEC_OwnInitEntry.closure, `PV_LIB_SPEC_OwnInitEntry.entry_nonempty])
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
        for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk, `PV_FN_THREAD_f361.Pre.mk] do
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
