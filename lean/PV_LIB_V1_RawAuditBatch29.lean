import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_Tls278Bound15, `PV_LIB_SPEC_Tls278Delivery16, `PV_LIB_SPEC_Tls278History15, `PV_LIB_SPEC_Tls278Lift15, `PV_LIB_SPEC_Tls278Native15, `PV_LIB_SPEC_Tls278Reached15, `PV_LIB_SPEC_Tls278Route15, `PV_LIB_SPEC_Tls278Trace15, `PV_LIB_SPEC_Tls278Values15, `PV_LIB_SPEC_Tls279Bound16, `PV_LIB_SPEC_Tls279Delivery16, `PV_LIB_SPEC_Tls279History16, `PV_LIB_SPEC_Tls279Native16, `PV_LIB_SPEC_Tls279Request16, `PV_LIB_SPEC_Tls279Route16, `PV_LIB_SPEC_Tls279Values16, `PV_LIB_SPEC_Tls59Data15, `PV_LIB_SPEC_Tls64Data16, `PV_LIB_SPEC_Tls68Data16, `PV_LIB_SPEC_Tls75Cells16, `PV_LIB_SPEC_Tls85Data16, `PV_LIB_SPEC_TlsAt54, `PV_LIB_SPEC_TlsAt55, `PV_LIB_SPEC_TlsAt58, `PV_LIB_SPEC_TlsAt59, `PV_LIB_SPEC_TlsAt63, `PV_LIB_SPEC_TlsAt64, `PV_LIB_SPEC_TlsAt67]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_Tls278Bound15.trigger, `PV_LIB_SPEC_Tls278Delivery16.transition, `PV_LIB_SPEC_Tls278History15.consumed, `PV_LIB_SPEC_Tls278History15.issued, `PV_LIB_SPEC_Tls278History15.site, `PV_LIB_SPEC_Tls278Lift15.clear, `PV_LIB_SPEC_Tls278Lift15.config, `PV_LIB_SPEC_Tls278Lift15.error, `PV_LIB_SPEC_Tls278Lift15.reached, `PV_LIB_SPEC_Tls278Lift15.source, `PV_LIB_SPEC_Tls278Native15.native, `PV_LIB_SPEC_Tls278Reached15.config, `PV_LIB_SPEC_Tls278Reached15.reached, `PV_LIB_SPEC_Tls278Reached15.request, `PV_LIB_SPEC_Tls278Reached15.result, `PV_LIB_SPEC_Tls278Reached15.wait, `PV_LIB_SPEC_Tls278Reached15.waiting, `PV_LIB_SPEC_Tls278Route15.fn, `PV_LIB_SPEC_Tls278Route15.route, `PV_LIB_SPEC_Tls278Trace15.trace, `PV_LIB_SPEC_Tls278Values15.fields, `PV_LIB_SPEC_Tls278Values15.pure, `PV_LIB_SPEC_Tls278Values15.token, `PV_LIB_SPEC_Tls278Values15.value, `PV_LIB_SPEC_Tls279Bound16.answer, `PV_LIB_SPEC_Tls279Bound16.different, `PV_LIB_SPEC_Tls279Bound16.trigger, `PV_LIB_SPEC_Tls279Delivery16.transition, `PV_LIB_SPEC_Tls279History16.consumed, `PV_LIB_SPEC_Tls279History16.issued, `PV_LIB_SPEC_Tls279History16.site, `PV_LIB_SPEC_Tls279Native16.different, `PV_LIB_SPEC_Tls279Native16.native, `PV_LIB_SPEC_Tls279Request16.config, `PV_LIB_SPEC_Tls279Request16.site, `PV_LIB_SPEC_Tls279Request16.source, `PV_LIB_SPEC_Tls279Request16.trace, `PV_LIB_SPEC_Tls279Route16.fn, `PV_LIB_SPEC_Tls279Route16.route, `PV_LIB_SPEC_Tls279Values16.fields, `PV_LIB_SPEC_Tls279Values16.pure, `PV_LIB_SPEC_Tls279Values16.token, `PV_LIB_SPEC_Tls279Values16.value, `PV_LIB_SPEC_Tls59Data15.after, `PV_LIB_SPEC_Tls59Data15.at59, `PV_LIB_SPEC_Tls59Data15.config, `PV_LIB_SPEC_Tls59Data15.nonnative, `PV_LIB_SPEC_Tls59Data15.origin, `PV_LIB_SPEC_Tls59Data15.request, `PV_LIB_SPEC_Tls59Data15.result, `PV_LIB_SPEC_Tls59Data15.store59, `PV_LIB_SPEC_Tls59Data15.token, `PV_LIB_SPEC_Tls59Data15.wait, `PV_LIB_SPEC_Tls59Data15.waiting, `PV_LIB_SPEC_Tls64Data16.after, `PV_LIB_SPEC_Tls64Data16.at64, `PV_LIB_SPEC_Tls64Data16.config, `PV_LIB_SPEC_Tls64Data16.nonnative, `PV_LIB_SPEC_Tls64Data16.origin, `PV_LIB_SPEC_Tls64Data16.request, `PV_LIB_SPEC_Tls64Data16.result, `PV_LIB_SPEC_Tls64Data16.store64, `PV_LIB_SPEC_Tls64Data16.token, `PV_LIB_SPEC_Tls64Data16.wait]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_Tls64Data16.waiting, `PV_LIB_SPEC_Tls68Data16.after, `PV_LIB_SPEC_Tls68Data16.at68, `PV_LIB_SPEC_Tls68Data16.config, `PV_LIB_SPEC_Tls68Data16.nonnative, `PV_LIB_SPEC_Tls68Data16.origin, `PV_LIB_SPEC_Tls68Data16.request, `PV_LIB_SPEC_Tls68Data16.result, `PV_LIB_SPEC_Tls68Data16.store68, `PV_LIB_SPEC_Tls68Data16.token, `PV_LIB_SPEC_Tls68Data16.wait, `PV_LIB_SPEC_Tls68Data16.waiting, `PV_LIB_SPEC_Tls75Cells16.callable, `PV_LIB_SPEC_Tls75Cells16.pointer, `PV_LIB_SPEC_Tls85Data16.after, `PV_LIB_SPEC_Tls85Data16.at85, `PV_LIB_SPEC_Tls85Data16.ordinary, `PV_LIB_SPEC_Tls85Data16.origin, `PV_LIB_SPEC_Tls85Data16.store85, `PV_LIB_SPEC_Tls85Data16.wait, `PV_LIB_SPEC_Tls85Data16.waiting, `PV_LIB_SPEC_TlsAt54.at54, `PV_LIB_SPEC_TlsAt54.config, `PV_LIB_SPEC_TlsAt54.initValue, `PV_LIB_SPEC_TlsAt54.no_native54, `PV_LIB_SPEC_TlsAt54.original53, `PV_LIB_SPEC_TlsAt54.original54, `PV_LIB_SPEC_TlsAt54.reached_poll, `PV_LIB_SPEC_TlsAt54.store51, `PV_LIB_SPEC_TlsAt54.store53, `PV_LIB_SPEC_TlsAt54.token, `PV_LIB_SPEC_TlsAt54.world54, `PV_LIB_SPEC_TlsAt55.at55, `PV_LIB_SPEC_TlsAt55.consume, `PV_LIB_SPEC_TlsAt55.context, `PV_LIB_SPEC_TlsAt55.ordinary, `PV_LIB_SPEC_TlsAt55.origin, `PV_LIB_SPEC_TlsAt55.original55, `PV_LIB_SPEC_TlsAt55.wait, `PV_LIB_SPEC_TlsAt58.at58, `PV_LIB_SPEC_TlsAt58.first_native, `PV_LIB_SPEC_TlsAt58.original58, `PV_LIB_SPEC_TlsAt58.world58, `PV_LIB_SPEC_TlsAt59.consume, `PV_LIB_SPEC_TlsAt59.context, `PV_LIB_SPEC_TlsAt59.original59, `PV_LIB_SPEC_TlsAt63.at63, `PV_LIB_SPEC_TlsAt63.consumed63, `PV_LIB_SPEC_TlsAt63.entry, `PV_LIB_SPEC_TlsAt63.handler, `PV_LIB_SPEC_TlsAt63.issued63, `PV_LIB_SPEC_TlsAt63.original63, `PV_LIB_SPEC_TlsAt63.result_bound, `PV_LIB_SPEC_TlsAt63.state63, `PV_LIB_SPEC_TlsAt63.world63, `PV_LIB_SPEC_TlsAt64.consume, `PV_LIB_SPEC_TlsAt64.context, `PV_LIB_SPEC_TlsAt64.original64, `PV_LIB_SPEC_TlsAt67.at67, `PV_LIB_SPEC_TlsAt67.consumed67, `PV_LIB_SPEC_TlsAt67.entry]
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
