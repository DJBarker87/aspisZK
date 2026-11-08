import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_CallbackStores, `PV_LIB_SPEC_CallbackV2Runtime, `PV_LIB_SPEC_CellBindings13, `PV_LIB_SPEC_CellPhysical13, `PV_LIB_SPEC_Composition, `PV_LIB_SPEC_ConcreteCaptures, `PV_LIB_SPEC_ConcreteEntry, `PV_LIB_SPEC_ConsumedHistory18, `PV_LIB_SPEC_ConsumedHistory19, `PV_LIB_SPEC_ContextAllocation18, `PV_LIB_SPEC_ContextContracts18, `PV_LIB_SPEC_ContextCounter18, `PV_LIB_SPEC_ContextCounterPost18, `PV_LIB_SPEC_ContextF018, `PV_LIB_SPEC_ContextF118, `PV_LIB_SPEC_ContextF12518, `PV_LIB_SPEC_ContextF1518, `PV_LIB_SPEC_ContextF16618]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_CallbackStores.packet_word, `PV_LIB_SPEC_CallbackStores.reply, `PV_LIB_SPEC_CallbackStores.resource_answer, `PV_LIB_SPEC_CallbackStores.success, `PV_LIB_SPEC_CallbackStores.tail, `PV_LIB_SPEC_CallbackV2Runtime.actions, `PV_LIB_SPEC_CallbackV2Runtime.control, `PV_LIB_SPEC_CallbackV2Runtime.preserves_owner_away, `PV_LIB_SPEC_CallbackV2Runtime.run, `PV_LIB_SPEC_CallbackV2Runtime.step, `PV_LIB_SPEC_CallbackV2Runtime.transition, `PV_LIB_SPEC_CellBindings13.new_value, `PV_LIB_SPEC_CellBindings13.old_value, `PV_LIB_SPEC_CellBindings13.reply, `PV_LIB_SPEC_CellBindings13.value, `PV_LIB_SPEC_CellPhysical13.away, `PV_LIB_SPEC_CellPhysical13.byte, `PV_LIB_SPEC_CellPhysical13.reply, `PV_LIB_SPEC_CellPhysical13.setByte, `PV_LIB_SPEC_Composition.JointNonempty, `PV_LIB_SPEC_Composition.Legacy14756, `PV_LIB_SPEC_Composition.legacy_joint_contradiction, `PV_LIB_SPEC_Composition.separate_witnesses_insufficient, `PV_LIB_SPEC_Composition.taggedPayload, `PV_LIB_SPEC_Composition.tagged_rejects_legacy, `PV_LIB_SPEC_ConcreteCaptures.bytes, `PV_LIB_SPEC_ConcreteCaptures.captures, `PV_LIB_SPEC_ConcreteCaptures.closure, `PV_LIB_SPEC_ConcreteCaptures.entry_nonempty, `PV_LIB_SPEC_ConcreteCaptures.fHeader, `PV_LIB_SPEC_ConcreteCaptures.f_typed, `PV_LIB_SPEC_ConcreteCaptures.nHeader, `PV_LIB_SPEC_ConcreteCaptures.n_bytes, `PV_LIB_SPEC_ConcreteCaptures.n_typed, `PV_LIB_SPEC_ConcreteCaptures.one, `PV_LIB_SPEC_ConcreteCaptures.places, `PV_LIB_SPEC_ConcreteCaptures.receivers, `PV_LIB_SPEC_ConcreteCaptures.runHeader, `PV_LIB_SPEC_ConcreteCaptures.run_bytes, `PV_LIB_SPEC_ConcreteCaptures.run_typed, `PV_LIB_SPEC_ConcreteCaptures.site, `PV_LIB_SPEC_ConcreteCaptures.state, `PV_LIB_SPEC_ConcreteCaptures.taskHeader, `PV_LIB_SPEC_ConcreteCaptures.tasks_typed, `PV_LIB_SPEC_ConcreteCaptures.zero, `PV_LIB_SPEC_ConcreteEntry.Value, `PV_LIB_SPEC_ConcreteEntry.dereference, `PV_LIB_SPEC_ConcreteEntry.environment, `PV_LIB_SPEC_ConcreteEntry.fields, `PV_LIB_SPEC_ConcreteEntry.fresh, `PV_LIB_SPEC_ConcreteEntry.input, `PV_LIB_SPEC_ConcreteEntry.joint, `PV_LIB_SPEC_ConcreteEntry.machine, `PV_LIB_SPEC_ConcreteEntry.numbered, `PV_LIB_SPEC_ConcreteEntry.owner, `PV_LIB_SPEC_ConcreteEntry.parameters, `PV_LIB_SPEC_ConcreteEntry.pre, `PV_LIB_SPEC_ConcreteEntry.primitives, `PV_LIB_SPEC_ConcreteEntry.reachable, `PV_LIB_SPEC_ConcreteEntry.reference, `PV_LIB_SPEC_ConcreteEntry.references, `PV_LIB_SPEC_ConcreteEntry.resources, `PV_LIB_SPEC_ConcreteEntry.store, `PV_LIB_SPEC_ConcreteEntry.validity]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_ConsumedHistory18.poll_consumed, `PV_LIB_SPEC_ConsumedHistory18.prefix_member, `PV_LIB_SPEC_ConsumedHistory18.run_member, `PV_LIB_SPEC_ConsumedHistory18.step_member, `PV_LIB_SPEC_ConsumedHistory19.poll_consumed, `PV_LIB_SPEC_ConsumedHistory19.prefix_member, `PV_LIB_SPEC_ConsumedHistory19.run_member, `PV_LIB_SPEC_ConsumedHistory19.step_member, `PV_LIB_SPEC_ContextAllocation18.AllocationWitness, `PV_LIB_SPEC_ContextAllocation18.Input, `PV_LIB_SPEC_ContextAllocation18.Representation, `PV_LIB_SPEC_ContextAllocation18.entry, `PV_LIB_SPEC_ContextContracts18.Before, `PV_LIB_SPEC_ContextContracts18.Contracts, `PV_LIB_SPEC_ContextContracts18.Implementations, `PV_LIB_SPEC_ContextCounter18.Behavior, `PV_LIB_SPEC_ContextCounter18.Observation, `PV_LIB_SPEC_ContextCounter18.counter_abstracted, `PV_LIB_SPEC_ContextCounter18.observe, `PV_LIB_SPEC_ContextCounter18.old_distinguishes, `PV_LIB_SPEC_ContextCounter18.sample, `PV_LIB_SPEC_ContextCounter18.sample_histories_ignored, `PV_LIB_SPEC_ContextCounter18.sample_numbered, `PV_LIB_SPEC_ContextCounter18.sample_owner, `PV_LIB_SPEC_ContextCounter18.source_cells, `PV_LIB_SPEC_ContextCounterPost18.Post, `PV_LIB_SPEC_ContextCounterPost18.ordinary, `PV_LIB_SPEC_ContextF018.Before, `PV_LIB_SPEC_ContextF018.Contract, `PV_LIB_SPEC_ContextF018.Input, `PV_LIB_SPEC_ContextF018.MachineSpec, `PV_LIB_SPEC_ContextF018.Post, `PV_LIB_SPEC_ContextF018.PostRoot, `PV_LIB_SPEC_ContextF018.Pre, `PV_LIB_SPEC_ContextF018.pre_same, `PV_LIB_SPEC_ContextF118.Before, `PV_LIB_SPEC_ContextF118.Contract, `PV_LIB_SPEC_ContextF118.Input, `PV_LIB_SPEC_ContextF118.MachineSpec, `PV_LIB_SPEC_ContextF118.Post, `PV_LIB_SPEC_ContextF118.Pre, `PV_LIB_SPEC_ContextF118.pre_same, `PV_LIB_SPEC_ContextF12518.Before, `PV_LIB_SPEC_ContextF12518.Contract, `PV_LIB_SPEC_ContextF12518.Input, `PV_LIB_SPEC_ContextF12518.MachineSpec, `PV_LIB_SPEC_ContextF12518.Post, `PV_LIB_SPEC_ContextF12518.Pre, `PV_LIB_SPEC_ContextF12518.pre_same, `PV_LIB_SPEC_ContextF1518.Before, `PV_LIB_SPEC_ContextF1518.Contract, `PV_LIB_SPEC_ContextF1518.Input, `PV_LIB_SPEC_ContextF1518.MachineSpec, `PV_LIB_SPEC_ContextF1518.Post, `PV_LIB_SPEC_ContextF1518.Pre, `PV_LIB_SPEC_ContextF1518.pre_same, `PV_LIB_SPEC_ContextF16618.Before, `PV_LIB_SPEC_ContextF16618.Contract, `PV_LIB_SPEC_ContextF16618.Input, `PV_LIB_SPEC_ContextF16618.MachineSpec, `PV_LIB_SPEC_ContextF16618.Post]
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
