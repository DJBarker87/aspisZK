import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_Boundary, `PV_LIB_SPEC_Delivery, `PV_LIB_SPEC_Composition, `PV_LIB_SPEC_Environment],
     #[`PV_LIB_SPEC_Boundary.State, `PV_LIB_SPEC_Boundary.Machine, `PV_LIB_SPEC_Boundary.step, `PV_LIB_SPEC_Boundary.run, `PV_LIB_SPEC_Boundary.ConsumedPending, `PV_LIB_SPEC_Boundary.OwnComplete, `PV_LIB_SPEC_Boundary.RepresentationGap, `PV_LIB_SPEC_Boundary.Terminal, `PV_LIB_SPEC_Boundary.Boundary, `PV_LIB_SPEC_Boundary.First, `PV_LIB_SPEC_Boundary.Diverges, `PV_LIB_SPEC_Boundary.Numbered, `PV_LIB_SPEC_Boundary.observe, `PV_LIB_SPEC_Boundary.first_unique, `PV_LIB_SPEC_Boundary.body_not_pending, `PV_LIB_SPEC_Boundary.abort_prefix, `PV_LIB_SPEC_Delivery.Terminal, `PV_LIB_SPEC_Delivery.Boundary, `PV_LIB_SPEC_Delivery.First, `PV_LIB_SPEC_Delivery.Diverges, `PV_LIB_SPEC_Delivery.run_succ, `PV_LIB_SPEC_Delivery.callback_return_not_boundary, `PV_LIB_SPEC_Delivery.first_unique, `PV_LIB_SPEC_Composition.taggedPayload, `PV_LIB_SPEC_Composition.Legacy14756, `PV_LIB_SPEC_Composition.tagged_rejects_legacy, `PV_LIB_SPEC_Composition.legacy_joint_contradiction, `PV_LIB_SPEC_Composition.JointNonempty, `PV_LIB_SPEC_Composition.separate_witnesses_insufficient, `PV_LIB_SPEC_Environment.Site, `PV_LIB_SPEC_Environment.Request, `PV_LIB_SPEC_Environment.Env, `PV_LIB_SPEC_Environment.Channel, `PV_LIB_SPEC_Environment.reply, `PV_LIB_SPEC_Environment.Law, `PV_LIB_SPEC_Environment.observe, `PV_LIB_SPEC_Environment.ObservedLaw, `PV_LIB_SPEC_Environment.functional, `PV_LIB_SPEC_Environment.observed_functional, `PV_LIB_SPEC_Environment.abort_prefix, `PV_LIB_SPEC_Environment.pendingEnv, `PV_LIB_SPEC_Environment.nonempty])
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
