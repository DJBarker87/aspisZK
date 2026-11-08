import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_B_F15_F167, `PV_LIB_B_F15_F167Fixed, `PV_LIB_B_F15_F9, `PV_LIB_B_F15_F93, `PV_LIB_B_F15_F93Fixed, `PV_LIB_B_F15_F9Fixed, `PV_LIB_B_F170_F277, `PV_LIB_B_F170_F278, `PV_LIB_B_F170_F279, `PV_LIB_B_F170_F280, `PV_LIB_B_F1_F10, `PV_LIB_B_F1_F10Fixed, `PV_LIB_B_F1_F9, `PV_LIB_B_F1_F9Fixed, `PV_LIB_B_F21Pending, `PV_LIB_B_F21_F32, `PV_LIB_B_F21_F33, `PV_LIB_B_F270_F279, `PV_LIB_B_F270_F280, `PV_LIB_B_F361_F279, `PV_LIB_B_F361_F280, `PV_LIB_B_F537_F612],
     #[`PV_LIB_B_F15_F167.source0, `PV_LIB_B_F15_F167.source1, `PV_LIB_B_F15_F167.source2, `PV_LIB_B_F15_F167.actual_machine0, `PV_LIB_B_F15_F167.actual_machine1, `PV_LIB_B_F15_F167.actual_machine2, `PV_LIB_B_F15_F167.caller_domain, `PV_LIB_B_F15_F167.closed_root, `PV_LIB_B_F15_F167.model, `PV_LIB_B_F15_F167.law, `PV_LIB_B_F15_F167Fixed.source0, `PV_LIB_B_F15_F167Fixed.source1, `PV_LIB_B_F15_F167Fixed.source2, `PV_LIB_B_F15_F167Fixed.actual_machine0, `PV_LIB_B_F15_F167Fixed.actual_machine1, `PV_LIB_B_F15_F167Fixed.actual_machine2, `PV_LIB_B_F15_F167Fixed.caller_domain, `PV_LIB_B_F15_F167Fixed.closed_root, `PV_LIB_B_F15_F167Fixed.model, `PV_LIB_B_F15_F167Fixed.law, `PV_LIB_B_F15_F9.source0, `PV_LIB_B_F15_F9.actual_machine0, `PV_LIB_B_F15_F9.caller_domain, `PV_LIB_B_F15_F9.closed_root, `PV_LIB_B_F15_F9.model, `PV_LIB_B_F15_F9.law, `PV_LIB_B_F15_F93.source0, `PV_LIB_B_F15_F93.actual_machine0, `PV_LIB_B_F15_F93.caller_domain, `PV_LIB_B_F15_F93.closed_root, `PV_LIB_B_F15_F93.model, `PV_LIB_B_F15_F93.law, `PV_LIB_B_F15_F93Fixed.source0, `PV_LIB_B_F15_F93Fixed.actual_machine0, `PV_LIB_B_F15_F93Fixed.caller_domain, `PV_LIB_B_F15_F93Fixed.closed_root, `PV_LIB_B_F15_F93Fixed.model, `PV_LIB_B_F15_F93Fixed.law, `PV_LIB_B_F15_F9Fixed.source0, `PV_LIB_B_F15_F9Fixed.actual_machine0, `PV_LIB_B_F15_F9Fixed.caller_domain, `PV_LIB_B_F15_F9Fixed.closed_root, `PV_LIB_B_F15_F9Fixed.model, `PV_LIB_B_F15_F9Fixed.law, `PV_LIB_B_F170_F277.model, `PV_LIB_B_F170_F277.law, `PV_LIB_B_F170_F277.caller_domain, `PV_LIB_B_F170_F277.certified, `PV_LIB_B_F170_F277.actual_machine, `PV_LIB_B_F170_F278.model, `PV_LIB_B_F170_F278.law, `PV_LIB_B_F170_F278.caller_domain, `PV_LIB_B_F170_F278.certified, `PV_LIB_B_F170_F278.actual_machine, `PV_LIB_B_F170_F279.model, `PV_LIB_B_F170_F279.law, `PV_LIB_B_F170_F279.caller_domain, `PV_LIB_B_F170_F279.certified, `PV_LIB_B_F170_F279.actual_machine, `PV_LIB_B_F170_F280.model, `PV_LIB_B_F170_F280.law, `PV_LIB_B_F170_F280.caller_domain, `PV_LIB_B_F170_F280.certified, `PV_LIB_B_F170_F280.actual_machine, `PV_LIB_B_F1_F10.source0, `PV_LIB_B_F1_F10.actual_machine0, `PV_LIB_B_F1_F10.caller_domain, `PV_LIB_B_F1_F10.closed_root, `PV_LIB_B_F1_F10.model, `PV_LIB_B_F1_F10.law, `PV_LIB_B_F1_F10Fixed.source0, `PV_LIB_B_F1_F10Fixed.actual_machine0, `PV_LIB_B_F1_F10Fixed.caller_domain, `PV_LIB_B_F1_F10Fixed.closed_root, `PV_LIB_B_F1_F10Fixed.model, `PV_LIB_B_F1_F10Fixed.law, `PV_LIB_B_F1_F9.source0, `PV_LIB_B_F1_F9.actual_machine0, `PV_LIB_B_F1_F9.caller_domain, `PV_LIB_B_F1_F9.closed_root, `PV_LIB_B_F1_F9.model, `PV_LIB_B_F1_F9.law, `PV_LIB_B_F1_F9Fixed.source0, `PV_LIB_B_F1_F9Fixed.actual_machine0, `PV_LIB_B_F1_F9Fixed.caller_domain, `PV_LIB_B_F1_F9Fixed.closed_root, `PV_LIB_B_F1_F9Fixed.model, `PV_LIB_B_F1_F9Fixed.law, `PV_LIB_B_F21Pending.LegacyPoll, `PV_LIB_B_F21Pending.NativePoll, `PV_LIB_B_F21Pending.Pending, `PV_LIB_B_F21Pending.forget, `PV_LIB_B_F21Pending.rejects_body, `PV_LIB_B_F21Pending.rejects_completed, `PV_LIB_B_F21_F32.source_arguments, `PV_LIB_B_F21_F32.caller_domain, `PV_LIB_B_F21_F32.model, `PV_LIB_B_F21_F32.law, `PV_LIB_B_F21_F32.certified, `PV_LIB_B_F21_F32.actual_machine, `PV_LIB_B_F21_F33.source_arguments, `PV_LIB_B_F21_F33.caller_domain, `PV_LIB_B_F21_F33.model, `PV_LIB_B_F21_F33.law, `PV_LIB_B_F21_F33.certified, `PV_LIB_B_F21_F33.actual_machine, `PV_LIB_B_F270_F279.source0, `PV_LIB_B_F270_F279.actual_machine0, `PV_LIB_B_F270_F279.caller_domain, `PV_LIB_B_F270_F279.closed_root, `PV_LIB_B_F270_F279.model, `PV_LIB_B_F270_F279.law, `PV_LIB_B_F270_F279.certified, `PV_LIB_B_F270_F280.source0, `PV_LIB_B_F270_F280.actual_machine0, `PV_LIB_B_F270_F280.caller_domain, `PV_LIB_B_F270_F280.closed_root, `PV_LIB_B_F270_F280.model, `PV_LIB_B_F270_F280.law, `PV_LIB_B_F270_F280.certified, `PV_LIB_B_F361_F279.source0, `PV_LIB_B_F361_F279.actual_machine0, `PV_LIB_B_F361_F279.caller_domain, `PV_LIB_B_F361_F279.closed_root, `PV_LIB_B_F361_F279.model, `PV_LIB_B_F361_F279.law, `PV_LIB_B_F361_F279.certified, `PV_LIB_B_F361_F280.source0, `PV_LIB_B_F361_F280.actual_machine0, `PV_LIB_B_F361_F280.caller_domain, `PV_LIB_B_F361_F280.closed_root, `PV_LIB_B_F361_F280.model, `PV_LIB_B_F361_F280.law, `PV_LIB_B_F361_F280.certified, `PV_LIB_B_F537_F612.source0, `PV_LIB_B_F537_F612.actual_machine0, `PV_LIB_B_F537_F612.caller_domain, `PV_LIB_B_F537_F612.closed_root, `PV_LIB_B_F537_F612.model, `PV_LIB_B_F537_F612.law, `PV_LIB_B_F537_F612.certified])
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
        for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk,
          `PV_THR2_LibrarySemantics_AtomicUsizeNew.Returned.mk] do
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
