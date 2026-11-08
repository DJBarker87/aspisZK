import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SLICE_Spec_f13, `PV_LIB_SLICE_Spec_f2, `PV_LIB_SLICE_Spec_f21, `PV_LIB_SLICE_Spec_f4, `PV_LIB_SLICE_Spec_f5, `PV_LIB_SLICE_Spec_f6, `PV_LIB_SLICE_Spec_f7, `PV_LIB_SLICE_Spec_f8, `PV_LIB_SLICE_Spec_f9, `PV_LIB_SLICE_TypedDrop, `PV_LIB_SPEC_ActiveAdoption19, `PV_LIB_SPEC_ActiveBoundary19]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SLICE_Spec_f13.MachineSpec, `PV_LIB_SLICE_Spec_f13.Post, `PV_LIB_SLICE_Spec_f13.Pre, `PV_LIB_SLICE_Spec_f13.start, `PV_LIB_SLICE_Spec_f2.Contract, `PV_LIB_SLICE_Spec_f2.Entry, `PV_LIB_SLICE_Spec_f2.MachineSpec, `PV_LIB_SLICE_Spec_f2.Post, `PV_LIB_SLICE_Spec_f2.Pre, `PV_LIB_SLICE_Spec_f2.start, `PV_LIB_SLICE_Spec_f21.Boundary, `PV_LIB_SLICE_Spec_f21.Contract, `PV_LIB_SLICE_Spec_f21.Entry, `PV_LIB_SLICE_Spec_f21.Environment, `PV_LIB_SLICE_Spec_f21.Event, `PV_LIB_SLICE_Spec_f21.First, `PV_LIB_SLICE_Spec_f21.Frame, `PV_LIB_SLICE_Spec_f21.FreshByte, `PV_LIB_SLICE_Spec_f21.FullFrame, `PV_LIB_SLICE_Spec_f21.Machine, `PV_LIB_SLICE_Spec_f21.MachineSpec, `PV_LIB_SLICE_Spec_f21.Observation, `PV_LIB_SLICE_Spec_f21.Outcome, `PV_LIB_SLICE_Spec_f21.Pending, `PV_LIB_SLICE_Spec_f21.Post, `PV_LIB_SLICE_Spec_f21.Pre, `PV_LIB_SLICE_Spec_f21.ResourceRequest, `PV_LIB_SLICE_Spec_f21.SourceFrame, `PV_LIB_SLICE_Spec_f21.Success, `PV_LIB_SLICE_Spec_f21.abort_prefix, `PV_LIB_SLICE_Spec_f21.construction_length, `PV_LIB_SLICE_Spec_f21.encodedLength, `PV_LIB_SLICE_Spec_f21.execution, `PV_LIB_SLICE_Spec_f21.final_length, `PV_LIB_SLICE_Spec_f21.first_unique, `PV_LIB_SLICE_Spec_f21.machine_implies_package, `PV_LIB_SLICE_Spec_f21.no_false_pending11, `PV_LIB_SLICE_Spec_f21.observe, `PV_LIB_SLICE_Spec_f21.package_success_forces_zero, `PV_LIB_SLICE_Spec_f21.pending_implies_old, `PV_LIB_SLICE_Spec_f21.pre_comparison, `PV_LIB_SLICE_Spec_f21.reference, `PV_LIB_SLICE_Spec_f21.start, `PV_LIB_SLICE_Spec_f21.statusView, `PV_LIB_SLICE_Spec_f21.storeView, `PV_LIB_SLICE_Spec_f4.Contract, `PV_LIB_SLICE_Spec_f4.Entry, `PV_LIB_SLICE_Spec_f4.MachineSpec, `PV_LIB_SLICE_Spec_f4.Post, `PV_LIB_SLICE_Spec_f4.Pre, `PV_LIB_SLICE_Spec_f4.start, `PV_LIB_SLICE_Spec_f5.Contract, `PV_LIB_SLICE_Spec_f5.Entry, `PV_LIB_SLICE_Spec_f5.MachineSpec, `PV_LIB_SLICE_Spec_f5.Post, `PV_LIB_SLICE_Spec_f5.Pre, `PV_LIB_SLICE_Spec_f5.start, `PV_LIB_SLICE_Spec_f6.Contract, `PV_LIB_SLICE_Spec_f6.Entry, `PV_LIB_SLICE_Spec_f6.MachineSpec, `PV_LIB_SLICE_Spec_f6.Post, `PV_LIB_SLICE_Spec_f6.Pre, `PV_LIB_SLICE_Spec_f6.start, `PV_LIB_SLICE_Spec_f7.Contract]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SLICE_Spec_f7.Entry, `PV_LIB_SLICE_Spec_f7.MachineSpec, `PV_LIB_SLICE_Spec_f7.Post, `PV_LIB_SLICE_Spec_f7.Pre, `PV_LIB_SLICE_Spec_f7.start, `PV_LIB_SLICE_Spec_f8.Contract, `PV_LIB_SLICE_Spec_f8.Entry, `PV_LIB_SLICE_Spec_f8.MachineSpec, `PV_LIB_SLICE_Spec_f8.Post, `PV_LIB_SLICE_Spec_f8.Pre, `PV_LIB_SLICE_Spec_f8.start, `PV_LIB_SLICE_Spec_f9.Contract, `PV_LIB_SLICE_Spec_f9.Entry, `PV_LIB_SLICE_Spec_f9.MachineSpec, `PV_LIB_SLICE_Spec_f9.Post, `PV_LIB_SLICE_Spec_f9.Pre, `PV_LIB_SLICE_Spec_f9.initialized, `PV_LIB_SLICE_Spec_f9.start, `PV_LIB_SLICE_Statements.ArrayClone, `PV_LIB_SLICE_Statements.ArrayEntry, `PV_LIB_SLICE_Statements.ArrayPre, `PV_LIB_SLICE_Statements.Boundary, `PV_LIB_SLICE_Statements.CapturePre, `PV_LIB_SLICE_Statements.Clone, `PV_LIB_SLICE_Statements.Entry, `PV_LIB_SLICE_Statements.Environment, `PV_LIB_SLICE_Statements.Event, `PV_LIB_SLICE_Statements.First, `PV_LIB_SLICE_Statements.Frame, `PV_LIB_SLICE_Statements.Machine, `PV_LIB_SLICE_Statements.MachineSpec, `PV_LIB_SLICE_Statements.Outcome, `PV_LIB_SLICE_Statements.Pending, `PV_LIB_SLICE_Statements.Post, `PV_LIB_SLICE_Statements.Pre, `PV_LIB_SLICE_Statements.Source, `PV_LIB_SLICE_Statements.Source.Valid, `PV_LIB_SLICE_Statements.column, `PV_LIB_SLICE_Statements.execution, `PV_LIB_SLICE_Statements.freshByte, `PV_LIB_SLICE_Statements.inRoot, `PV_LIB_SLICE_Statements.reference, `PV_LIB_SLICE_Statements.sources, `PV_LIB_SLICE_Statements.start, `PV_LIB_SLICE_Statements.vector, `PV_LIB_SLICE_Statements.wrappedValue, `PV_LIB_SLICE_Statements.wrapper, `PV_LIB_SLICE_TypedDrop.certified, `PV_LIB_SLICE_TypedDrop.selected, `PV_LIB_SPEC_ActiveAdoption19.history, `PV_LIB_SPEC_ActiveAdoption19.original141, `PV_LIB_SPEC_ActiveAdoption19.original85, `PV_LIB_SPEC_ActiveAdoption19.predicate_prefix, `PV_LIB_SPEC_ActiveAdoption19.preserved, `PV_LIB_SPEC_ActiveAdoption19.replies85, `PV_LIB_SPEC_ActiveAdoption19.step, `PV_LIB_SPEC_ActiveAdoption19.values_prefix, `PV_LIB_SPEC_ActiveAdoption19.world85, `PV_LIB_SPEC_ActiveBoundary19.changed, `PV_LIB_SPEC_ActiveBoundary19.effects, `PV_LIB_SPEC_ActiveBoundary19.full]
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
