import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_F316Enter22013, `PV_LIB_A_F316Full41013, `PV_LIB_A_F316History13, `PV_LIB_A_F316Prefix13, `PV_LIB_A_F316ToInvoke13, `PV_LIB_A_F5BoundaryGap16, `PV_LIB_A_F5Call16, `PV_LIB_A_F5CallbackObstruction16, `PV_LIB_A_F5CallbackStall16, `PV_LIB_A_F5CallbackTrap16, `PV_LIB_A_F5ClosurePending16, `PV_LIB_A_F5Entry16, `PV_LIB_A_F5FullEntry16, `PV_LIB_A_F5FullPush16, `PV_LIB_A_F5History16, `PV_LIB_A_F5Prefix16, `PV_LIB_A_F6Arc12, `PV_LIB_A_F6CallbackHistory14, `PV_LIB_A_F6Captures13, `PV_LIB_A_F6CatchHistory13, `PV_LIB_A_F6Constructors12, `PV_LIB_A_F6Counter11, `PV_LIB_A_F6Data12, `PV_LIB_A_F6DeliveryTransportV2, `PV_LIB_A_F6EarlyHistory11, `PV_LIB_A_F6Enter12513, `PV_LIB_A_F6History12, `PV_LIB_A_F6IssuedHistory13, `PV_LIB_A_F6Panic11, `PV_LIB_A_F6Prefix11]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_F316Enter22013.after, `PV_LIB_A_F316Enter22013.programs, `PV_LIB_A_F316Enter22013.run, `PV_LIB_A_F316Enter22013.shape, `PV_LIB_A_F316Enter22013.steps, `PV_LIB_A_F316Full41013.run, `PV_LIB_A_F316Full41013.source, `PV_LIB_A_F316Full41013.trace, `PV_LIB_A_F316Full41013.waiting, `PV_LIB_A_F316History13.run, `PV_LIB_A_F316History13.stage4, `PV_LIB_A_F316History13.steps, `PV_LIB_A_F316Prefix13.after, `PV_LIB_A_F316Prefix13.off, `PV_LIB_A_F316Prefix13.run, `PV_LIB_A_F316Prefix13.shape, `PV_LIB_A_F316Prefix13.steps, `PV_LIB_A_F316ToInvoke13.after, `PV_LIB_A_F316ToInvoke13.off, `PV_LIB_A_F316ToInvoke13.run, `PV_LIB_A_F316ToInvoke13.shape, `PV_LIB_A_F316ToInvoke13.steps, `PV_LIB_A_F5BoundaryGap16.boundary_lookup, `PV_LIB_A_F5BoundaryGap16.full_lookup, `PV_LIB_A_F5BoundaryGap16.no_agreement, `PV_LIB_A_F5BoundaryGap16.no_trace, `PV_LIB_A_F5Call16.original132, `PV_LIB_A_F5Call16.run, `PV_LIB_A_F5Call16.shape, `PV_LIB_A_F5CallbackObstruction16.answer_pending, `PV_LIB_A_F5CallbackObstruction16.not_arc, `PV_LIB_A_F5CallbackStall16.quiet, `PV_LIB_A_F5CallbackStall16.transition, `PV_LIB_A_F5CallbackTrap16.no_body_entry, `PV_LIB_A_F5CallbackTrap16.ordinary, `PV_LIB_A_F5CallbackTrap16.step, `PV_LIB_A_F5CallbackTrap16.trapped, `PV_LIB_A_F5CallbackTrap16.undefined_run, `PV_LIB_A_F5CallbackTrap16.undefined_step, `PV_LIB_A_F5ClosurePending16.backend_pending, `PV_LIB_A_F5ClosurePending16.unforwarded, `PV_LIB_A_F5ClosurePending16.unselected, `PV_LIB_A_F5Entry16.lookup, `PV_LIB_A_F5Entry16.run, `PV_LIB_A_F5FullEntry16.closure_bound, `PV_LIB_A_F5FullEntry16.key_bound, `PV_LIB_A_F5FullEntry16.original141, `PV_LIB_A_F5FullPush16.original133, `PV_LIB_A_F5FullPush16.push, `PV_LIB_A_F5History16.original123, `PV_LIB_A_F5History16.original131, `PV_LIB_A_F5Prefix16.clear, `PV_LIB_A_F5Prefix16.run, `PV_LIB_A_F5Prefix16.source, `PV_LIB_A_F5Prefix16.trace, `PV_LIB_A_F6Arc12.run, `PV_LIB_A_F6Arc12.shape, `PV_LIB_A_F6Arc12.sites, `PV_LIB_A_F6Arc12.storage, `PV_LIB_A_F6Arc12.trace, `PV_LIB_A_F6Arc12.waiting, `PV_LIB_A_F6CallbackHistory14.continuation, `PV_LIB_A_F6CallbackHistory14.history, `PV_LIB_A_F6CallbackHistory14.stage7]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_F6CallbackHistory14.steps, `PV_LIB_A_F6Captures13.after, `PV_LIB_A_F6Captures13.off, `PV_LIB_A_F6Captures13.run, `PV_LIB_A_F6Captures13.shape, `PV_LIB_A_F6Captures13.steps, `PV_LIB_A_F6CatchHistory13.continuation, `PV_LIB_A_F6CatchHistory13.history, `PV_LIB_A_F6CatchHistory13.stage7, `PV_LIB_A_F6CatchHistory13.steps, `PV_LIB_A_F6Constructors12.counter, `PV_LIB_A_F6Constructors12.counter_word, `PV_LIB_A_F6Constructors12.entry121, `PV_LIB_A_F6Constructors12.entry123, `PV_LIB_A_F6Constructors12.panic_word, `PV_LIB_A_F6Constructors12.panicked, `PV_LIB_A_F6Counter11.call_quiet, `PV_LIB_A_F6Counter11.history18, `PV_LIB_A_F6Counter11.issue, `PV_LIB_A_F6Counter11.poll, `PV_LIB_A_F6Counter11.wait_quiet, `PV_LIB_A_F6Data12.after, `PV_LIB_A_F6Data12.finish, `PV_LIB_A_F6Data12.run, `PV_LIB_A_F6Data12.source, `PV_LIB_A_F6Data12.steps, `PV_LIB_A_F6Data12.trace, `PV_LIB_A_F6DeliveryTransportV2.prefix_identity, `PV_LIB_A_F6EarlyHistory11.after, `PV_LIB_A_F6EarlyHistory11.continuation, `PV_LIB_A_F6EarlyHistory11.history, `PV_LIB_A_F6EarlyHistory11.panicStore, `PV_LIB_A_F6EarlyHistory11.steps, `PV_LIB_A_F6EarlyHistory11.threadStore, `PV_LIB_A_F6Enter12513.after, `PV_LIB_A_F6Enter12513.programs, `PV_LIB_A_F6Enter12513.run, `PV_LIB_A_F6Enter12513.shape, `PV_LIB_A_F6Enter12513.steps, `PV_LIB_A_F6History12.after, `PV_LIB_A_F6History12.afterData, `PV_LIB_A_F6History12.afterStorage, `PV_LIB_A_F6History12.continuation, `PV_LIB_A_F6History12.history, `PV_LIB_A_F6History12.steps, `PV_LIB_A_F6IssuedHistory13.after, `PV_LIB_A_F6IssuedHistory13.continuation, `PV_LIB_A_F6IssuedHistory13.history, `PV_LIB_A_F6IssuedHistory13.steps, `PV_LIB_A_F6Panic11.call_quiet, `PV_LIB_A_F6Panic11.issue, `PV_LIB_A_F6Panic11.poll, `PV_LIB_A_F6Panic11.segment3, `PV_LIB_A_F6Panic11.storage, `PV_LIB_A_F6Panic11.wait_quiet, `PV_LIB_A_F6Prefix11.literal_bound, `PV_LIB_A_F6Prefix11.prologue_run, `PV_LIB_A_F6Prefix11.result16, `PV_LIB_A_F6Prefix11.shape, `PV_LIB_A_F6Prefix11.sites, `PV_LIB_A_F6Prefix11.steps16]
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
