import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_Emitted214, `PV_LIB_A_Emitted486, `PV_LIB_A_Emitted584, `PV_LIB_A_Emitted608, `PV_LIB_A_EmittedDropBinding, `PV_LIB_A_ExactDestructMethods, `PV_LIB_A_ExpressionFrame14, `PV_LIB_A_F124CallResolvers15, `PV_LIB_A_F124EntryData14, `PV_LIB_A_F124LocalResolver15, `PV_LIB_A_F124ReturnedFrame14, `PV_LIB_A_F125Enter21913, `PV_LIB_A_F125Prologue13, `PV_LIB_A_F166Builder12, `PV_LIB_A_F166Chains12, `PV_LIB_A_F166History12, `PV_LIB_A_F170History16, `PV_LIB_A_F170Result16, `PV_LIB_A_F170Return16, `PV_LIB_A_F170Tail15, `PV_LIB_A_F17Finish16, `PV_LIB_A_F17History16, `PV_LIB_A_F17Return16, `PV_LIB_A_F17Value16, `PV_LIB_A_F17ValueLift16, `PV_LIB_A_F208Prefix14, `PV_LIB_A_F219CallbackHistory14, `PV_LIB_A_F219Enter31614, `PV_LIB_A_F219Enter316Any14, `PV_LIB_A_F219Full13413, `PV_LIB_A_F219Issue31813, `PV_LIB_A_F219Prologue13, `PV_LIB_A_F219Selected14, `PV_LIB_A_F219To31813, `PV_LIB_A_F220Enter20814, `PV_LIB_A_F220Prefix14, `PV_LIB_A_F2Finish16, `PV_LIB_A_F2History16]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_Emitted214.program, `PV_LIB_A_Emitted486.program, `PV_LIB_A_Emitted584.program, `PV_LIB_A_Emitted608.program, `PV_LIB_A_EmittedDropBinding.exact_program, `PV_LIB_A_EmittedDropBinding.fnPtr608, `PV_LIB_A_EmittedDropBinding.programs, `PV_LIB_A_EmittedDropBinding.selected608, `PV_LIB_A_ExactDestructMethods.adtImpl, `PV_LIB_A_ExactDestructMethods.byType, `PV_LIB_A_ExactDestructMethods.concrete, `PV_LIB_A_ExactDestructMethods.implementation, `PV_LIB_A_ExactDestructMethods.methodGenerics, `PV_LIB_A_ExactDestructMethods.method_types, `PV_LIB_A_ExactDestructMethods.resolve, `PV_LIB_A_ExpressionFrame14.Safe, `PV_LIB_A_ExpressionFrame14.bind_frame, `PV_LIB_A_ExpressionFrame14.evaluate_frame, `PV_LIB_A_F124CallResolvers15.actual, `PV_LIB_A_F124CallResolvers15.calls, `PV_LIB_A_F124EntryData14.bounded, `PV_LIB_A_F124EntryData14.installed, `PV_LIB_A_F124EntryData14.pre, `PV_LIB_A_F124EntryData14.provenance, `PV_LIB_A_F124EntryData14.valid, `PV_LIB_A_F124LocalResolver15.fixed, `PV_LIB_A_F124ReturnedFrame14.counter_mono, `PV_LIB_A_F124ReturnedFrame14.numbered, `PV_LIB_A_F124ReturnedFrame14.post_and_frame, `PV_LIB_A_F124ReturnedFrame14.source_frame, `PV_LIB_A_F124ReturnedFrame14.stack_numbering, `PV_LIB_A_F125Enter21913.after, `PV_LIB_A_F125Enter21913.programs, `PV_LIB_A_F125Enter21913.run, `PV_LIB_A_F125Enter21913.shape, `PV_LIB_A_F125Enter21913.steps, `PV_LIB_A_F125Prologue13.after, `PV_LIB_A_F125Prologue13.off, `PV_LIB_A_F125Prologue13.run, `PV_LIB_A_F125Prologue13.shape, `PV_LIB_A_F125Prologue13.steps, `PV_LIB_A_F166Builder12.run, `PV_LIB_A_F166Builder12.trace, `PV_LIB_A_F166Builder12.waiting, `PV_LIB_A_F166Chains12.captures, `PV_LIB_A_F166Chains12.captures_sites, `PV_LIB_A_F166Chains12.captures_trace, `PV_LIB_A_F166Chains12.prologue, `PV_LIB_A_F166Chains12.prologue_sites, `PV_LIB_A_F166Chains12.prologue_trace, `PV_LIB_A_F166History12.after, `PV_LIB_A_F166History12.afterBuilder, `PV_LIB_A_F166History12.afterCaptures, `PV_LIB_A_F166History12.afterPrologue, `PV_LIB_A_F166History12.run, `PV_LIB_A_F166History12.steps, `PV_LIB_A_F170History16.original94, `PV_LIB_A_F170Result16.computed, `PV_LIB_A_F170Return16.cell, `PV_LIB_A_F170Return16.execution_ext, `PV_LIB_A_F170Return16.original96, `PV_LIB_A_F170Tail15.off, `PV_LIB_A_F170Tail15.run, `PV_LIB_A_F170Tail15.shape]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_F17Finish16.clear, `PV_LIB_A_F17Finish16.run, `PV_LIB_A_F17Finish16.trace, `PV_LIB_A_F17History16.cell, `PV_LIB_A_F17History16.original104, `PV_LIB_A_F17Return16.cell, `PV_LIB_A_F17Return16.original112, `PV_LIB_A_F17Value16.trace, `PV_LIB_A_F17ValueLift16.carrier, `PV_LIB_A_F17ValueLift16.clear, `PV_LIB_A_F17ValueLift16.source, `PV_LIB_A_F208Prefix14.off, `PV_LIB_A_F208Prefix14.run, `PV_LIB_A_F208Prefix14.shape, `PV_LIB_A_F219CallbackHistory14.after, `PV_LIB_A_F219CallbackHistory14.off, `PV_LIB_A_F219CallbackHistory14.run, `PV_LIB_A_F219CallbackHistory14.shape, `PV_LIB_A_F219CallbackHistory14.steps, `PV_LIB_A_F219Enter31614.exact_tail, `PV_LIB_A_F219Enter31614.finish, `PV_LIB_A_F219Enter31614.run, `PV_LIB_A_F219Enter316Any14.exact_tail, `PV_LIB_A_F219Enter316Any14.issue, `PV_LIB_A_F219Enter316Any14.run, `PV_LIB_A_F219Full13413.run, `PV_LIB_A_F219Full13413.source, `PV_LIB_A_F219Full13413.trace, `PV_LIB_A_F219Full13413.waiting, `PV_LIB_A_F219Issue31813.after, `PV_LIB_A_F219Issue31813.programs, `PV_LIB_A_F219Issue31813.run, `PV_LIB_A_F219Issue31813.shape, `PV_LIB_A_F219Issue31813.steps, `PV_LIB_A_F219Prologue13.after, `PV_LIB_A_F219Prologue13.off, `PV_LIB_A_F219Prologue13.run, `PV_LIB_A_F219Prologue13.shape, `PV_LIB_A_F219Prologue13.steps, `PV_LIB_A_F219Selected14.invoke, `PV_LIB_A_F219Selected14.issue, `PV_LIB_A_F219Selected14.operands, `PV_LIB_A_F219Selected14.selected, `PV_LIB_A_F219To31813.after, `PV_LIB_A_F219To31813.off, `PV_LIB_A_F219To31813.run, `PV_LIB_A_F219To31813.shape, `PV_LIB_A_F219To31813.steps, `PV_LIB_A_F220Enter20814.after, `PV_LIB_A_F220Enter20814.programs, `PV_LIB_A_F220Enter20814.run, `PV_LIB_A_F220Enter20814.shape, `PV_LIB_A_F220Enter20814.steps, `PV_LIB_A_F220Prefix14.off, `PV_LIB_A_F220Prefix14.run, `PV_LIB_A_F220Prefix14.shape, `PV_LIB_A_F2Finish16.clear, `PV_LIB_A_F2Finish16.run, `PV_LIB_A_F2Finish16.trace, `PV_LIB_A_F2History16.cell, `PV_LIB_A_F2History16.original116]
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
