import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SLICE_Spec_f21, `PV_LIB_SLICE_Spec_f13, `PV_LIB_SLICE_Spec_f6, `PV_LIB_SLICE_Spec_f5, `PV_LIB_SLICE_Spec_f8, `PV_LIB_SLICE_Spec_f7, `PV_LIB_SLICE_Spec_f9, `PV_LIB_SLICE_Spec_f4, `PV_LIB_SLICE_Spec_f2, `PV_LIB_SLICE_Spec_f1, `PV_LIB_SLICE_Spec_f0, `PV_LIB_SLICE_Spec_Source7Joint],
     #[`PV_LIB_SLICE_Spec_f21.FreshByte, `PV_LIB_SLICE_Spec_f21.FullFrame, `PV_LIB_SLICE_Spec_f21.Post, `PV_LIB_SLICE_Spec_f21.Contract, `PV_LIB_SLICE_Statements.Machine, `PV_LIB_SLICE_Statements.Environment, `PV_LIB_SLICE_Statements.MachineSpec, `PV_LIB_SLICE_Statements.Outcome, `PV_LIB_SLICE_Statements.Event, `PV_LIB_SLICE_Statements.Entry, `PV_LIB_SLICE_Statements.start, `PV_LIB_SLICE_Statements.execution, `PV_LIB_SLICE_Statements.Pre, `PV_LIB_SLICE_Statements.Source, `PV_LIB_SLICE_Statements.vector, `PV_LIB_SLICE_Statements.Source.Valid, `PV_LIB_SLICE_Statements.Clone, `PV_LIB_SLICE_Statements.Pending, `PV_LIB_SLICE_Statements.Boundary, `PV_LIB_SLICE_Statements.First, `PV_LIB_SLICE_Statements.reference, `PV_LIB_SLICE_Statements.inRoot, `PV_LIB_SLICE_Statements.freshByte, `PV_LIB_SLICE_Statements.Frame, `PV_LIB_SLICE_Statements.Post, `PV_LIB_SLICE_Spec_f13.Entry, `PV_LIB_SLICE_Spec_f13.MachineSpec, `PV_LIB_SLICE_Spec_f13.start, `PV_LIB_SLICE_Spec_f13.Pre, `PV_LIB_SLICE_Spec_f13.Post, `PV_LIB_SLICE_Spec_f13.Contract, `PV_LIB_SLICE_Statements.ArrayEntry, `PV_LIB_SLICE_Statements.sources, `PV_LIB_SLICE_Statements.column, `PV_LIB_SLICE_Statements.wrapper, `PV_LIB_SLICE_Statements.wrappedValue, `PV_LIB_SLICE_Statements.ArrayPre, `PV_LIB_SLICE_Statements.CapturePre, `PV_LIB_SLICE_Statements.ArrayClone, `PV_LIB_SLICE_Spec_f6.Entry, `PV_LIB_SLICE_Spec_f6.MachineSpec, `PV_LIB_SLICE_Spec_f6.start, `PV_LIB_SLICE_Spec_f6.Pre, `PV_LIB_SLICE_Spec_f6.Post, `PV_LIB_SLICE_Spec_f6.Contract, `PV_LIB_SLICE_Spec_f5.Entry, `PV_LIB_SLICE_Spec_f5.MachineSpec, `PV_LIB_SLICE_Spec_f5.start, `PV_LIB_SLICE_Spec_f5.Pre, `PV_LIB_SLICE_Spec_f5.Post, `PV_LIB_SLICE_Spec_f5.Contract, `PV_LIB_SLICE_Spec_f8.Entry, `PV_LIB_SLICE_Spec_f8.MachineSpec, `PV_LIB_SLICE_Spec_f8.start, `PV_LIB_SLICE_Spec_f8.Pre, `PV_LIB_SLICE_Spec_f8.Post, `PV_LIB_SLICE_Spec_f8.Contract, `PV_LIB_SLICE_Spec_f7.Entry, `PV_LIB_SLICE_Spec_f7.MachineSpec, `PV_LIB_SLICE_Spec_f7.start, `PV_LIB_SLICE_Spec_f7.Pre, `PV_LIB_SLICE_Spec_f7.Post, `PV_LIB_SLICE_Spec_f7.Contract, `PV_LIB_SLICE_Spec_f9.Entry, `PV_LIB_SLICE_Spec_f9.MachineSpec, `PV_LIB_SLICE_Spec_f9.start, `PV_LIB_SLICE_Spec_f9.Pre, `PV_LIB_SLICE_Spec_f9.initialized, `PV_LIB_SLICE_Spec_f9.Post, `PV_LIB_SLICE_Spec_f9.Contract, `PV_LIB_SLICE_Spec_f4.Entry, `PV_LIB_SLICE_Spec_f4.MachineSpec, `PV_LIB_SLICE_Spec_f4.start, `PV_LIB_SLICE_Spec_f4.Pre, `PV_LIB_SLICE_Spec_f4.Post, `PV_LIB_SLICE_Spec_f4.Contract, `PV_LIB_SLICE_Spec_f2.Entry, `PV_LIB_SLICE_Spec_f2.MachineSpec, `PV_LIB_SLICE_Spec_f2.start, `PV_LIB_SLICE_Spec_f2.Pre, `PV_LIB_SLICE_Spec_f2.Post, `PV_LIB_SLICE_Spec_f2.Contract, `PV_LIB_SLICE_Spec_f1.Entry, `PV_LIB_SLICE_Spec_f1.MachineSpec, `PV_LIB_SLICE_Spec_f1.start, `PV_LIB_SLICE_Spec_f1.Pre, `PV_LIB_SLICE_Spec_f1.Post, `PV_LIB_SLICE_Spec_f1.Contract, `PV_LIB_SLICE_Spec_f0.Entry, `PV_LIB_SLICE_Spec_f0.MachineSpec, `PV_LIB_SLICE_Spec_f0.start, `PV_LIB_SLICE_Spec_f0.Pre, `PV_LIB_SLICE_Spec_f0.Post, `PV_LIB_SLICE_Spec_f0.Contract, `PV_LIB_SLICE_Spec_Source7Joint.header, `PV_LIB_SLICE_Spec_Source7Joint.state, `PV_LIB_SLICE_Spec_Source7Joint.foundation, `PV_LIB_SLICE_Spec_Source7Joint.values_empty, `PV_LIB_SLICE_Spec_Source7Joint.ids, `PV_LIB_SLICE_Spec_Source7Joint.wf, `PV_LIB_SLICE_Spec_Source7Joint.typed, `PV_LIB_SLICE_Spec_Source7Joint.owned, `PV_LIB_SLICE_Spec_Source7Joint.selected_header, `PV_LIB_SLICE_Spec_Source7Joint.indexed, `PV_LIB_SLICE_Spec_Source7Joint.valid, `PV_LIB_SLICE_Spec_Source7Joint.base, `PV_LIB_SLICE_Spec_Source7Joint.ctrl, `PV_LIB_SLICE_Spec_Source7Joint.external, `PV_LIB_SLICE_Spec_Source7Joint.backend, `PV_LIB_SLICE_Spec_Source7Joint.handler, `PV_LIB_SLICE_Spec_Source7Joint.machine, `PV_LIB_SLICE_Spec_Source7Joint.environment, `PV_LIB_SLICE_Spec_Source7Joint.machine_spec, `PV_LIB_SLICE_Spec_Source7Joint.source, `PV_LIB_SLICE_Spec_Source7Joint.root, `PV_LIB_SLICE_Spec_Source7Joint.store, `PV_LIB_SLICE_Spec_Source7Joint.entry, `PV_LIB_SLICE_Spec_Source7Joint.source_valid, `PV_LIB_SLICE_Spec_Source7Joint.pre, `PV_LIB_SLICE_Spec_Source7Joint.joint])
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
        for aux in #[`PV_LIB_SLICE_Spec_f21.Entry.mk, `PV_LIB_SLICE_Spec_f21.Pre.mk, `PV_LIB_SLICE_Spec_f21.ResourceRequest.mk, `PV_LIB_SLICE_Spec_f21.Environment.mk, `PV_LIB_SLICE_Spec_f21.MachineSpec.mk, `PV_LIB_SLICE_Statements.Entry.mk, `PV_LIB_SLICE_Statements.Pre.mk, `PV_LIB_SLICE_Statements.Source.mk, `PV_LIB_SLICE_Spec_f13.Entry.mk, `PV_LIB_SLICE_Statements.ArrayEntry.mk, `PV_LIB_SLICE_Spec_f0.Entry.mk, `PV_STX2_ToVecCallSummary.Entry.mk, `PV_STX2_ToVecCallSummary.Pre.mk, `PV_STX2_ToVecCallSummary.MachineSpec.mk, `PV_STX2_ToVecCallSummary.Success.mk, `PV_STX2_Source7EntryReferenceValid.Source7EntryOwned'''''.mk, `PV_STX2_Source7EntryOwnedAligned.Source7EntryOwned''''.mk, `PV_STX2_Source7EntryOwnedIndexed.Source7EntryOwned'''.mk, `PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed.mk, `PV_STX2_OwnerAllocationWellFormed.OwnerWellFormed.mk, `PV_STX2_OwnerActivationWellFormed.OwnerWellFormed.mk, `PV_STX2_ToVecCallReferenceEntry.Pre.mk, `PV_STX2_ToVecCallBytePost.Pre.mk, `PV_STX2_ToVecCallEntryInvariant.Pre.mk, `PV_STX2_ToVecCallArgumentEntry.Pre.mk] do
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
