import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_StoreActionTable, `PV_LIB_A_StoreActionMachine, `PV_LIB_A_ActionAdequacyGap, `PV_LIB_A_ReplyAdequacyGap, `PV_LIB_A_ActionAnswers],
     #[`PV_LIB_StoreActionTable.v2, `PV_LIB_StoreActionTable.coverage, `PV_LIB_StoreActionTable.interpret, `PV_LIB_StoreActionTable.weak_cas, `PV_LIB_StoreActionTable.strong_cas, `PV_LIB_StoreActionTable.clone_all_answers, `PV_LIB_StoreActionTable.scope_overflow, `PV_LIB_StoreActionTable.select, `PV_LIB_StoreActionTable.deliver, `PV_LIB_StoreActionTable.step, `PV_LIB_StoreActionTable.agreement, `PV_LIB_StoreActionTable.native, `PV_LIB_StoreActionTable.effects, `PV_LIB_StoreActionTable.advance_agreement, `PV_LIB_A_ActionAdequacyGap.set_selected, `PV_LIB_A_ActionAdequacyGap.aggregate_set_unsupported, `PV_LIB_A_ActionAdequacyGap.aggregate_prefix_defined, `PV_LIB_A_ActionAdequacyGap.aggregate_delivery_undefined, `PV_LIB_A_ActionAdequacyGap.last_drop_unsupported, `PV_LIB_A_ActionAdequacyGap.installed_wrappers_missing, `PV_LIB_A_ReplyAdequacyGap.pending_reply, `PV_LIB_A_ReplyAdequacyGap.panic_reply, `PV_LIB_A_ReplyAdequacyGap.pending_not_retained, `PV_LIB_A_ReplyAdequacyGap.panic_not_retained, `PV_LIB_A_ActionAnswers.weak_failure, `PV_LIB_A_ActionAnswers.strong_failure, `PV_LIB_A_ActionAnswers.weak_failure_delivery, `PV_LIB_A_ActionAnswers.cas_pending, `PV_LIB_A_ActionAnswers.cas_fault])
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
        for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk] do
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
