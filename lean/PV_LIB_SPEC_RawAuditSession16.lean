import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_Tls64Data16, `PV_LIB_SPEC_NativeDelivery16, `PV_LIB_SPEC_Tls278Delivery16, `PV_LIB_SPEC_TlsAt64, `PV_LIB_SPEC_Tls279Values16, `PV_LIB_SPEC_Tls279Route16, `PV_LIB_SPEC_Tls279Native16, `PV_LIB_SPEC_Tls279Bound16, `PV_LIB_SPEC_Tls279Request16, `PV_LIB_SPEC_Tls279History16, `PV_LIB_SPEC_TlsAt67, `PV_LIB_SPEC_Tls68Data16, `PV_LIB_SPEC_Tls279Delivery16, `PV_LIB_SPEC_TlsAt68, `PV_LIB_SPEC_TlsForward16, `PV_LIB_SPEC_TlsForwardLift16, `PV_LIB_SPEC_TlsAt75, `PV_LIB_SPEC_TlsCallable16, `PV_LIB_SPEC_Tls75Cells16, `PV_LIB_SPEC_TlsCallableLift16, `PV_LIB_SPEC_TlsCallableHistory16, `PV_LIB_SPEC_TlsAt84, `PV_LIB_SPEC_Tls18Bound16, `PV_LIB_SPEC_Tls18Reached16, `PV_LIB_SPEC_Tls85Data16, `PV_LIB_SPEC_Tls18Delivery16, `PV_LIB_SPEC_TlsAt85, `PV_LIB_SPEC_ActiveReplacement16, `PV_LIB_SPEC_LaneAJoins16, `PV_LIB_SPEC_BinaryStack16],
     #[`PV_LIB_SPEC_Tls64Data16.token, `PV_LIB_SPEC_Tls64Data16.result, `PV_LIB_SPEC_Tls64Data16.config, `PV_LIB_SPEC_Tls64Data16.request, `PV_LIB_SPEC_Tls64Data16.wait, `PV_LIB_SPEC_Tls64Data16.origin, `PV_LIB_SPEC_Tls64Data16.store64, `PV_LIB_SPEC_Tls64Data16.after, `PV_LIB_SPEC_Tls64Data16.at64, `PV_LIB_SPEC_Tls64Data16.waiting, `PV_LIB_SPEC_Tls64Data16.nonnative, `PV_LIB_SPEC_NativeDelivery16.full, `PV_LIB_SPEC_Tls278Delivery16.transition, `PV_LIB_SPEC_TlsAt64.context, `PV_LIB_SPEC_TlsAt64.consume, `PV_LIB_SPEC_TlsAt64.original64, `PV_LIB_SPEC_Tls279Values16.token, `PV_LIB_SPEC_Tls279Values16.value, `PV_LIB_SPEC_Tls279Values16.pure, `PV_LIB_SPEC_Tls279Values16.fields, `PV_LIB_SPEC_Tls279Route16.fn, `PV_LIB_SPEC_Tls279Route16.route, `PV_LIB_SPEC_Tls279Native16.different, `PV_LIB_SPEC_Tls279Native16.native, `PV_LIB_SPEC_Tls279Bound16.different, `PV_LIB_SPEC_Tls279Bound16.trigger, `PV_LIB_SPEC_Tls279Bound16.answer, `PV_LIB_SPEC_Tls279Request16.trace, `PV_LIB_SPEC_Tls279Request16.site, `PV_LIB_SPEC_Tls279Request16.config, `PV_LIB_SPEC_Tls279Request16.source, `PV_LIB_SPEC_Tls279History16.site, `PV_LIB_SPEC_Tls279History16.issued, `PV_LIB_SPEC_Tls279History16.consumed, `PV_LIB_SPEC_TlsAt67.handler, `PV_LIB_SPEC_TlsAt67.at67, `PV_LIB_SPEC_TlsAt67.result_bound, `PV_LIB_SPEC_TlsAt67.original67, `PV_LIB_SPEC_TlsAt67.state67, `PV_LIB_SPEC_TlsAt67.issued67, `PV_LIB_SPEC_TlsAt67.consumed67, `PV_LIB_SPEC_TlsAt67.world67, `PV_LIB_SPEC_TlsAt67.entry, `PV_LIB_SPEC_Tls68Data16.token, `PV_LIB_SPEC_Tls68Data16.result, `PV_LIB_SPEC_Tls68Data16.config, `PV_LIB_SPEC_Tls68Data16.request, `PV_LIB_SPEC_Tls68Data16.wait, `PV_LIB_SPEC_Tls68Data16.origin, `PV_LIB_SPEC_Tls68Data16.store68, `PV_LIB_SPEC_Tls68Data16.after, `PV_LIB_SPEC_Tls68Data16.at68, `PV_LIB_SPEC_Tls68Data16.waiting, `PV_LIB_SPEC_Tls68Data16.nonnative, `PV_LIB_SPEC_Tls279Delivery16.transition, `PV_LIB_SPEC_TlsAt68.context, `PV_LIB_SPEC_TlsAt68.consume, `PV_LIB_SPEC_TlsAt68.original68, `PV_LIB_SPEC_TlsForward16.trace, `PV_LIB_SPEC_TlsForward16.prepared, `PV_LIB_SPEC_TlsForward16.source, `PV_LIB_SPEC_TlsForwardLift16.clear, `PV_LIB_SPEC_TlsForwardLift16.source, `PV_LIB_SPEC_TlsAt75.handler, `PV_LIB_SPEC_TlsAt75.store75, `PV_LIB_SPEC_TlsAt75.at75, `PV_LIB_SPEC_TlsAt75.cell, `PV_LIB_SPEC_TlsAt75.original75, `PV_LIB_SPEC_TlsAt75.state75, `PV_LIB_SPEC_TlsAt75.consumed75, `PV_LIB_SPEC_TlsCallable16.trace, `PV_LIB_SPEC_TlsCallable16.config, `PV_LIB_SPEC_TlsCallable16.source, `PV_LIB_SPEC_Tls75Cells16.pointer, `PV_LIB_SPEC_Tls75Cells16.callable, `PV_LIB_SPEC_TlsCallableLift16.clear, `PV_LIB_SPEC_TlsCallableLift16.source, `PV_LIB_SPEC_TlsCallableHistory16.site, `PV_LIB_SPEC_TlsCallableHistory16.issued, `PV_LIB_SPEC_TlsAt84.config, `PV_LIB_SPEC_TlsAt84.at84, `PV_LIB_SPEC_TlsAt84.stage75, `PV_LIB_SPEC_TlsAt84.dereference, `PV_LIB_SPEC_TlsAt84.original84, `PV_LIB_SPEC_TlsAt84.state84, `PV_LIB_SPEC_TlsAt84.issued84, `PV_LIB_SPEC_TlsAt84.consumed84, `PV_LIB_SPEC_Tls18Bound16.token, `PV_LIB_SPEC_Tls18Bound16.arguments, `PV_LIB_SPEC_Tls18Bound16.request, `PV_LIB_SPEC_Tls18Bound16.different, `PV_LIB_SPEC_Tls18Bound16.selected, `PV_LIB_SPEC_Tls18Bound16.trigger, `PV_LIB_SPEC_Tls18Bound16.answer, `PV_LIB_SPEC_Tls18Reached16.read_nil, `PV_LIB_SPEC_Tls18Reached16.source, `PV_LIB_SPEC_Tls18Reached16.active, `PV_LIB_SPEC_Tls18Reached16.reached, `PV_LIB_SPEC_Tls85Data16.wait, `PV_LIB_SPEC_Tls85Data16.origin, `PV_LIB_SPEC_Tls85Data16.store85, `PV_LIB_SPEC_Tls85Data16.after, `PV_LIB_SPEC_Tls85Data16.at85, `PV_LIB_SPEC_Tls85Data16.waiting, `PV_LIB_SPEC_Tls85Data16.ordinary, `PV_LIB_SPEC_Tls18Delivery16.lookup, `PV_LIB_SPEC_Tls18Delivery16.transition, `PV_LIB_SPEC_TlsAt85.context, `PV_LIB_SPEC_TlsAt85.consume, `PV_LIB_SPEC_TlsAt85.original85, `PV_LIB_SPEC_ActiveReplacement16.physical, `PV_LIB_SPEC_ActiveReplacement16.source_write, `PV_LIB_SPEC_LaneAJoins16.history, `PV_LIB_SPEC_LaneAJoins16.BodyEntry, `PV_LIB_SPEC_LaneAJoins16.OriginalToF6, `PV_LIB_SPEC_LaneAJoins16.RangeEntry, `PV_LIB_SPEC_LaneAJoins16.F6ToRange, `PV_LIB_SPEC_LaneAJoins16.RangeToF361, `PV_LIB_SPEC_LaneAJoins16.F361ToInit, `PV_LIB_SPEC_LaneAJoins16.Joins, `PV_LIB_SPEC_LaneAJoins16.original85, `PV_LIB_SPEC_BinaryStack16.scopeRsp, `PV_LIB_SPEC_BinaryStack16.spawnRsp, `PV_LIB_SPEC_BinaryStack16.prologues, `PV_LIB_SPEC_BinaryStack16.argument_slots, `PV_LIB_SPEC_BinaryStack16.frame, `PV_LIB_SPEC_BinaryStack16.coordinates])
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
