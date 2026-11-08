import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_ContextMachine18, `PV_LIB_SPEC_ContextMachine19, `PV_LIB_SPEC_ContextOwnInit18, `PV_LIB_SPEC_ContextPost18, `PV_LIB_SPEC_ContextReply18, `PV_LIB_SPEC_ControlHistory, `PV_LIB_SPEC_ControlJoint, `PV_LIB_SPEC_ControlRuntime, `PV_LIB_SPEC_Cut92Composition, `PV_LIB_SPEC_Delivery, `PV_LIB_SPEC_DisjointCaptures18, `PV_LIB_SPEC_DisjointEntry18, `PV_LIB_SPEC_DisjointPre18, `PV_LIB_SPEC_F361Whole]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_ContextMachine18.run, `PV_LIB_SPEC_ContextMachine18.run_same, `PV_LIB_SPEC_ContextMachine18.source, `PV_LIB_SPEC_ContextMachine18.source_spec, `PV_LIB_SPEC_ContextMachine18.start, `PV_LIB_SPEC_ContextMachine19.Before, `PV_LIB_SPEC_ContextMachine19.Behavior, `PV_LIB_SPEC_ContextMachine19.Machine, `PV_LIB_SPEC_ContextMachine19.MachineSpec, `PV_LIB_SPEC_ContextMachine19.history_same, `PV_LIB_SPEC_ContextMachine19.observe, `PV_LIB_SPEC_ContextMachine19.retained_prefix, `PV_LIB_SPEC_ContextMachine19.run, `PV_LIB_SPEC_ContextMachine19.run_same, `PV_LIB_SPEC_ContextMachine19.source, `PV_LIB_SPEC_ContextMachine19.source_spec, `PV_LIB_SPEC_ContextOwnInit18.Before, `PV_LIB_SPEC_ContextOwnInit18.Boundary, `PV_LIB_SPEC_ContextOwnInit18.Contract, `PV_LIB_SPEC_ContextOwnInit18.First, `PV_LIB_SPEC_ContextOwnInit18.Input, `PV_LIB_SPEC_ContextOwnInit18.MachineSpec, `PV_LIB_SPEC_ContextOwnInit18.Post, `PV_LIB_SPEC_ContextOwnInit18.Pre, `PV_LIB_SPEC_ContextOwnInit18.Representation, `PV_LIB_SPEC_ContextOwnInit18.pre_same, `PV_LIB_SPEC_ContextPost18.Post, `PV_LIB_SPEC_ContextPost18.ordinary, `PV_LIB_SPEC_ContextReply18.bound_answer, `PV_LIB_SPEC_ContextReply18.delivery84, `PV_LIB_SPEC_ContextReply18.fixed_answer, `PV_LIB_SPEC_ContextReply18.history_same, `PV_LIB_SPEC_ContextReply18.no_reply_identity, `PV_LIB_SPEC_ControlHistory.Invariant, `PV_LIB_SPEC_ControlHistory.append_record, `PV_LIB_SPEC_ControlHistory.context_origin, `PV_LIB_SPEC_ControlHistory.initial, `PV_LIB_SPEC_ControlHistory.original, `PV_LIB_SPEC_ControlHistory.record_mono, `PV_LIB_SPEC_ControlHistory.run, `PV_LIB_SPEC_ControlHistory.step, `PV_LIB_SPEC_ControlJoint.EntryMachinePremises, `PV_LIB_SPEC_ControlJoint.NativeFacets, `PV_LIB_SPEC_ControlJoint.TableRequirement, `PV_LIB_SPEC_ControlJoint.entryMachine, `PV_LIB_SPEC_ControlJoint.nativeFacets, `PV_LIB_SPEC_ControlJoint.withTable, `PV_LIB_SPEC_ControlRuntime.Machine, `PV_LIB_SPEC_ControlRuntime.MachineSpec, `PV_LIB_SPEC_ControlRuntime.controlStep, `PV_LIB_SPEC_ControlRuntime.execute, `PV_LIB_SPEC_ControlRuntime.issuing, `PV_LIB_SPEC_ControlRuntime.ordinary, `PV_LIB_SPEC_ControlRuntime.recordIssue, `PV_LIB_SPEC_ControlRuntime.run, `PV_LIB_SPEC_ControlRuntime.source, `PV_LIB_SPEC_ControlRuntime.step, `PV_LIB_SPEC_Cut92Composition.AllocationBranch, `PV_LIB_SPEC_Cut92Composition.Contracts, `PV_LIB_SPEC_Cut92Composition.Implementations, `PV_LIB_SPEC_Cut92Composition.OwnContract, `PV_LIB_SPEC_Cut92Composition.Witness, `PV_LIB_SPEC_D984.AwayAgreement, `PV_LIB_SPEC_D984.Behavior]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_D984.Boundary, `PV_LIB_SPEC_D984.ConsumedPending, `PV_LIB_SPEC_D984.Diverges, `PV_LIB_SPEC_D984.Event, `PV_LIB_SPEC_D984.First, `PV_LIB_SPEC_D984.FullStoreActionTable, `PV_LIB_SPEC_D984.Handler, `PV_LIB_SPEC_D984.Machine, `PV_LIB_SPEC_D984.Numbered, `PV_LIB_SPEC_D984.OwnComplete, `PV_LIB_SPEC_D984.RegisteredValidity, `PV_LIB_SPEC_D984.State, `PV_LIB_SPEC_D984.TableAdequacy, `PV_LIB_SPEC_D984.Terminal, `PV_LIB_SPEC_D984.Writer, `PV_LIB_SPEC_D984.lookup, `PV_LIB_SPEC_D984.observe, `PV_LIB_SPEC_D984.ownerStep, `PV_LIB_SPEC_D984.programs, `PV_LIB_SPEC_D984.run, `PV_LIB_SPEC_D984.selected, `PV_LIB_SPEC_D984.step, `PV_LIB_SPEC_Delivery.Boundary, `PV_LIB_SPEC_Delivery.Diverges, `PV_LIB_SPEC_Delivery.First, `PV_LIB_SPEC_Delivery.Terminal, `PV_LIB_SPEC_Delivery.callback_return_not_boundary, `PV_LIB_SPEC_Delivery.first_unique, `PV_LIB_SPEC_Delivery.run_succ, `PV_LIB_SPEC_DisjointCaptures18.bytes, `PV_LIB_SPEC_DisjointCaptures18.captures, `PV_LIB_SPEC_DisjointCaptures18.closure, `PV_LIB_SPEC_DisjointCaptures18.entry_nonempty, `PV_LIB_SPEC_DisjointCaptures18.fHeader, `PV_LIB_SPEC_DisjointCaptures18.f_typed, `PV_LIB_SPEC_DisjointCaptures18.nHeader, `PV_LIB_SPEC_DisjointCaptures18.n_bytes, `PV_LIB_SPEC_DisjointCaptures18.n_typed, `PV_LIB_SPEC_DisjointCaptures18.one, `PV_LIB_SPEC_DisjointCaptures18.places, `PV_LIB_SPEC_DisjointCaptures18.receivers, `PV_LIB_SPEC_DisjointCaptures18.runHeader, `PV_LIB_SPEC_DisjointCaptures18.run_bytes, `PV_LIB_SPEC_DisjointCaptures18.run_typed, `PV_LIB_SPEC_DisjointCaptures18.site, `PV_LIB_SPEC_DisjointCaptures18.state, `PV_LIB_SPEC_DisjointCaptures18.taskHeader, `PV_LIB_SPEC_DisjointCaptures18.tasks_typed, `PV_LIB_SPEC_DisjointCaptures18.zero, `PV_LIB_SPEC_DisjointEntry18.hooksSlot, `PV_LIB_SPEC_DisjointEntry18.input, `PV_LIB_SPEC_DisjointEntry18.memory_before, `PV_LIB_SPEC_DisjointEntry18.slot, `PV_LIB_SPEC_DisjointEntry18.state, `PV_LIB_SPEC_DisjointEntry18.store, `PV_LIB_SPEC_DisjointEntry18.tlsState, `PV_LIB_SPEC_DisjointPre18.captured, `PV_LIB_SPEC_DisjointPre18.f_typed, `PV_LIB_SPEC_DisjointPre18.fresh, `PV_LIB_SPEC_DisjointPre18.memory_before, `PV_LIB_SPEC_DisjointPre18.n_bytes]
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
