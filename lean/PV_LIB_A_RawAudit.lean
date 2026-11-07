import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_A_NativeLeaves, `PV_LIB_A_Unique612, `PV_LIB_A_UniqueBinding, `PV_LIB_A_SourceWriters, `PV_LIB_A_PureCalls, `PV_LIB_A_PurePoll, `PV_LIB_A_PureValues, `PV_LIB_A_WriterNative, `PV_LIB_A_Numbering, `PV_LIB_A_TypedDrop178, `PV_LIB_A_Range165, `PV_LIB_A_Residual280],
     #[`PV_LIB_A_NativeLeaves.certified277, `PV_LIB_A_NativeLeaves.certified278, `PV_LIB_A_NativeLeaves.certified279, `PV_LIB_A_NativeLeaves.certified280, `PV_LIB_A_NativeLeaves.certified612, `PV_LIB_A_Unique612.installed, `PV_LIB_A_UniqueBinding.callee, `PV_LIB_A_UniqueBinding.installed, `PV_LIB_A_SourceWriters.installed, `PV_LIB_A_SourceWriters.meanings, `PV_LIB_A_PureCalls.certified277, `PV_LIB_A_PureCalls.certified278, `PV_LIB_A_PureCalls.certified279, `PV_LIB_A_PureCalls.certified280, `PV_LIB_A_PureCalls.worlds, `PV_LIB_A_PureCalls.delivered_value, `PV_LIB_A_PureCalls.asRef_source_local, `PV_LIB_A_PurePoll.unlisted_poll, `PV_LIB_A_PurePoll.noncatch, `PV_LIB_A_PurePoll.installed277, `PV_LIB_A_PurePoll.installed278, `PV_LIB_A_PurePoll.installed279, `PV_LIB_A_PurePoll.installed280, `PV_LIB_A_PureValues.source_local278, `PV_LIB_A_PureValues.source_local279, `PV_LIB_A_WriterNative.certified9, `PV_LIB_A_WriterNative.certified10, `PV_LIB_A_WriterNative.certified93, `PV_LIB_A_WriterNative.certified167, `PV_LIB_A_Numbering.original_entry, `PV_LIB_A_Numbering.child_entry, `PV_LIB_A_Numbering.lower_bound, `PV_LIB_A_TypedDrop178.installed, `PV_LIB_A_Range165.old_contract_allows_range, `PV_LIB_A_Range165.sourceRange_distinct, `PV_LIB_A_Range165.sourceRange_not_null, `PV_LIB_A_Range165.reply_exact, `PV_LIB_A_Range165.certified, `PV_LIB_A_Range165.old_contract_allows_null, `PV_LIB_A_Residual280.certified, `PV_LIB_A_Residual280.source_local, `PV_LIB_A_Residual280.old_contract_allows_ok, `PV_LIB_A_Residual280.constructors_distinct])
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
