import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_B_F361_F279, `PV_LIB_B_F361_F280, `PV_LIB_B_F537_F612, `PV_LIB_Box443, `PV_LIB_Box458, `PV_LIB_Box537, `PV_LIB_BoxNew, `PV_LIB_Clone214, `PV_LIB_Drop, `PV_LIB_NativeGraph, `PV_LIB_PureLeaves, `PV_LIB_Registry, `PV_LIB_RootNative, `PV_LIB_SLICE_BoundedRun, `PV_LIB_SLICE_F32, `PV_LIB_SLICE_F33, `PV_LIB_SLICE_FoundationEntry, `PV_LIB_SLICE_RuntimeDrop, `PV_LIB_SLICE_Spec_Source7Joint, `PV_LIB_SLICE_Spec_f0, `PV_LIB_SLICE_Spec_f1, `PV_LIB_SLICE_Spec_f13]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_B_F361_F279.law, `PV_LIB_B_F361_F279.model, `PV_LIB_B_F361_F279.source0, `PV_LIB_B_F361_F280.actual_machine0, `PV_LIB_B_F361_F280.caller_domain, `PV_LIB_B_F361_F280.certified, `PV_LIB_B_F361_F280.closed_root, `PV_LIB_B_F361_F280.law, `PV_LIB_B_F361_F280.model, `PV_LIB_B_F361_F280.source0, `PV_LIB_B_F537_F612.actual_machine0, `PV_LIB_B_F537_F612.caller_domain, `PV_LIB_B_F537_F612.certified, `PV_LIB_B_F537_F612.closed_root, `PV_LIB_B_F537_F612.law, `PV_LIB_B_F537_F612.model, `PV_LIB_B_F537_F612.source0, `PV_LIB_Box443.installed, `PV_LIB_Box443.internal_reached, `PV_LIB_Box443.law, `PV_LIB_Box443.model, `PV_LIB_Box458.certified, `PV_LIB_Box458.installed, `PV_LIB_Box458.internal_reached, `PV_LIB_Box458.law, `PV_LIB_Box458.model, `PV_LIB_Box537.installed, `PV_LIB_Box537.internal_reached, `PV_LIB_Box537.law, `PV_LIB_Box537.model, `PV_LIB_BoxNew.certified, `PV_LIB_BoxNew.law, `PV_LIB_BoxNew.model, `PV_LIB_Clone214.certified, `PV_LIB_Clone214.law, `PV_LIB_Clone214.model, `PV_LIB_Drop.certified, `PV_LIB_Drop.law, `PV_LIB_Drop.model, `PV_LIB_NativeGraph.certified, `PV_LIB_PureLeaves.certified134, `PV_LIB_PureLeaves.certified217, `PV_LIB_PureLeaves.certified312, `PV_LIB_PureLeaves.certified313, `PV_LIB_PureLeaves.certified320, `PV_LIB_PureLeaves.certified344, `PV_LIB_PureLeaves.law134, `PV_LIB_PureLeaves.law217, `PV_LIB_PureLeaves.law312, `PV_LIB_PureLeaves.law313, `PV_LIB_PureLeaves.law320, `PV_LIB_PureLeaves.law344, `PV_LIB_PureLeaves.model134, `PV_LIB_PureLeaves.model217, `PV_LIB_PureLeaves.model312, `PV_LIB_PureLeaves.model313, `PV_LIB_PureLeaves.model320, `PV_LIB_PureLeaves.model344, `PV_LIB_Registry.certified, `PV_LIB_RootNative.certified171, `PV_LIB_RootNative.certified268, `PV_LIB_RootNative.certified3, `PV_LIB_RootNative.certified4, `PV_LIB_RootNative.law171]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_RootNative.law268, `PV_LIB_RootNative.law3, `PV_LIB_RootNative.law4, `PV_LIB_RootNative.model171, `PV_LIB_RootNative.model268, `PV_LIB_RootNative.model3, `PV_LIB_RootNative.model4, `PV_LIB_SLICE_BoundedRun.least, `PV_LIB_SLICE_BoundedRun.selected, `PV_LIB_SLICE_F32.certified, `PV_LIB_SLICE_F32.functional, `PV_LIB_SLICE_F33.certified, `PV_LIB_SLICE_F33.functional, `PV_LIB_SLICE_FoundationEntry.column, `PV_LIB_SLICE_FoundationEntry.discharge, `PV_LIB_SLICE_FoundationEntry.exact_obligation, `PV_LIB_SLICE_FoundationEntry.forget, `PV_LIB_SLICE_FoundationEntry.necessary, `PV_LIB_SLICE_RuntimeDrop.certified, `PV_LIB_SLICE_RuntimeDrop.functional, `PV_LIB_SLICE_RuntimeDrop.installed, `PV_LIB_SLICE_Spec_Source7Joint.backend, `PV_LIB_SLICE_Spec_Source7Joint.base, `PV_LIB_SLICE_Spec_Source7Joint.ctrl, `PV_LIB_SLICE_Spec_Source7Joint.entry, `PV_LIB_SLICE_Spec_Source7Joint.environment, `PV_LIB_SLICE_Spec_Source7Joint.external, `PV_LIB_SLICE_Spec_Source7Joint.foundation, `PV_LIB_SLICE_Spec_Source7Joint.handler, `PV_LIB_SLICE_Spec_Source7Joint.header, `PV_LIB_SLICE_Spec_Source7Joint.ids, `PV_LIB_SLICE_Spec_Source7Joint.indexed, `PV_LIB_SLICE_Spec_Source7Joint.joint, `PV_LIB_SLICE_Spec_Source7Joint.machine, `PV_LIB_SLICE_Spec_Source7Joint.machine_spec, `PV_LIB_SLICE_Spec_Source7Joint.owned, `PV_LIB_SLICE_Spec_Source7Joint.pre, `PV_LIB_SLICE_Spec_Source7Joint.root, `PV_LIB_SLICE_Spec_Source7Joint.selected_header, `PV_LIB_SLICE_Spec_Source7Joint.source, `PV_LIB_SLICE_Spec_Source7Joint.source_valid, `PV_LIB_SLICE_Spec_Source7Joint.state, `PV_LIB_SLICE_Spec_Source7Joint.store, `PV_LIB_SLICE_Spec_Source7Joint.typed, `PV_LIB_SLICE_Spec_Source7Joint.valid, `PV_LIB_SLICE_Spec_Source7Joint.values_empty, `PV_LIB_SLICE_Spec_Source7Joint.wf, `PV_LIB_SLICE_Spec_f0.Contract, `PV_LIB_SLICE_Spec_f0.Entry, `PV_LIB_SLICE_Spec_f0.MachineSpec, `PV_LIB_SLICE_Spec_f0.Post, `PV_LIB_SLICE_Spec_f0.Pre, `PV_LIB_SLICE_Spec_f0.start, `PV_LIB_SLICE_Spec_f1.Contract, `PV_LIB_SLICE_Spec_f1.Entry, `PV_LIB_SLICE_Spec_f1.MachineSpec, `PV_LIB_SLICE_Spec_f1.Post, `PV_LIB_SLICE_Spec_f1.Pre, `PV_LIB_SLICE_Spec_f1.start, `PV_LIB_SLICE_Spec_f13.Contract, `PV_LIB_SLICE_Spec_f13.Entry]
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
