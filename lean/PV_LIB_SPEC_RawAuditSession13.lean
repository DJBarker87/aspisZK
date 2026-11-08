import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_AtomicBindings13, `PV_LIB_SPEC_ThreadId13, `PV_LIB_SPEC_TlsBindings13, `PV_LIB_SPEC_Native13, `PV_LIB_SPEC_Entry13, `PV_LIB_SPEC_EntryPre13, `PV_LIB_SPEC_ArcPhysicalGap13, `PV_LIB_SPEC_CellBindings13, `PV_LIB_SPEC_ArcPhysical13, `PV_LIB_SPEC_CellPhysical13, `PV_LIB_SPEC_ScopePhysical13, `PV_LIB_SPEC_BoundNative13, `PV_LIB_SPEC_InitializedWords13, `PV_LIB_SPEC_Success13, `PV_LIB_SPEC_History13, `PV_LIB_SPEC_Builder269, `PV_LIB_SPEC_PrefixNative13, `PV_LIB_SPEC_PrefixEnvironment13, `PV_LIB_SPEC_TlsRecheck13, `PV_LIB_SPEC_PrefixHistory13],
     #[`PV_LIB_SPEC_AtomicBindings13.entry, `PV_LIB_SPEC_AtomicBindings13.load, `PV_LIB_SPEC_AtomicBindings13.reply, `PV_LIB_SPEC_AtomicBindings13.other, `PV_LIB_SPEC_AtomicBindings13.effects, `PV_LIB_SPEC_AtomicBindings13.config, `PV_LIB_SPEC_AtomicBindings13.args, `PV_LIB_SPEC_AtomicBindings13.constructor_load, `PV_LIB_SPEC_ThreadId13.counterOffset, `PV_LIB_SPEC_ThreadId13.value, `PV_LIB_SPEC_ThreadId13.reply, `PV_LIB_SPEC_ThreadId13.stored_counter, `PV_LIB_SPEC_ThreadId13.other, `PV_LIB_SPEC_ThreadId13.successful_ghost, `PV_LIB_SPEC_TlsBindings13.Slot, `PV_LIB_SPEC_TlsBindings13.read, `PV_LIB_SPEC_TlsBindings13.selected, `PV_LIB_SPEC_TlsBindings13.value, `PV_LIB_SPEC_TlsBindings13.reply, `PV_LIB_SPEC_TlsBindings13.world, `PV_LIB_SPEC_Native13.Cut, `PV_LIB_SPEC_Native13.core, `PV_LIB_SPEC_Native13.answer, `PV_LIB_SPEC_Native13.handler, `PV_LIB_SPEC_Native13.ordinary_framed, `PV_LIB_SPEC_Native13.transition, `PV_LIB_SPEC_Native13.control, `PV_LIB_SPEC_Native13.step, `PV_LIB_SPEC_Native13.run, `PV_LIB_SPEC_Native13.actions, `PV_LIB_SPEC_Native13.preserves_owner_away, `PV_LIB_SPEC_Entry13.slot, `PV_LIB_SPEC_Entry13.store, `PV_LIB_SPEC_Entry13.state, `PV_LIB_SPEC_Entry13.input, `PV_LIB_SPEC_Entry13.active, `PV_LIB_SPEC_Entry13.native_thread, `PV_LIB_SPEC_Entry13.source_active, `PV_LIB_SPEC_EntryPre13.memory_before, `PV_LIB_SPEC_EntryPre13.receivers, `PV_LIB_SPEC_EntryPre13.run_bytes, `PV_LIB_SPEC_EntryPre13.n_bytes, `PV_LIB_SPEC_EntryPre13.run_typed, `PV_LIB_SPEC_EntryPre13.n_typed, `PV_LIB_SPEC_EntryPre13.f_typed, `PV_LIB_SPEC_EntryPre13.tasks_typed, `PV_LIB_SPEC_EntryPre13.owner, `PV_LIB_SPEC_EntryPre13.captured, `PV_LIB_SPEC_EntryPre13.pre, `PV_LIB_SPEC_ArcPhysicalGap13.drops_physical_write, `PV_LIB_SPEC_ArcPhysicalGap13.byte_conflict, `PV_LIB_SPEC_CellBindings13.value, `PV_LIB_SPEC_CellBindings13.reply, `PV_LIB_SPEC_CellBindings13.old_value, `PV_LIB_SPEC_CellBindings13.new_value, `PV_LIB_SPEC_ArcPhysical13.operands, `PV_LIB_SPEC_ArcPhysical13.reply, `PV_LIB_SPEC_ArcPhysical13.write_away, `PV_LIB_SPEC_ArcPhysical13.one_to_two, `PV_LIB_SPEC_CellPhysical13.reply, `PV_LIB_SPEC_CellPhysical13.setByte, `PV_LIB_SPEC_CellPhysical13.byte, `PV_LIB_SPEC_CellPhysical13.away, `PV_LIB_SPEC_ScopePhysical13.operands, `PV_LIB_SPEC_ScopePhysical13.reply, `PV_LIB_SPEC_ScopePhysical13.one_to_two, `PV_LIB_SPEC_BoundNative13.Cut, `PV_LIB_SPEC_BoundNative13.core, `PV_LIB_SPEC_BoundNative13.answer, `PV_LIB_SPEC_BoundNative13.handler, `PV_LIB_SPEC_BoundNative13.ordinary_framed, `PV_LIB_SPEC_BoundNative13.transition, `PV_LIB_SPEC_BoundNative13.control, `PV_LIB_SPEC_BoundNative13.step, `PV_LIB_SPEC_BoundNative13.run, `PV_LIB_SPEC_BoundNative13.actions, `PV_LIB_SPEC_BoundNative13.preserves_owner_away, `PV_LIB_SPEC_InitializedWords13.one, `PV_LIB_SPEC_InitializedWords13.inner, `PV_LIB_SPEC_InitializedWords13.counter_bytes, `PV_LIB_SPEC_InitializedWords13.tls_bytes, `PV_LIB_SPEC_InitializedWords13.counter, `PV_LIB_SPEC_InitializedWords13.tls, `PV_LIB_SPEC_InitializedWords13.id_value, `PV_LIB_SPEC_Success13.native, `PV_LIB_SPEC_Success13.environment, `PV_LIB_SPEC_Success13.parameters, `PV_LIB_SPEC_Success13.pre, `PV_LIB_SPEC_Success13.allocations, `PV_LIB_SPEC_History13.step, `PV_LIB_SPEC_History13.initial, `PV_LIB_SPEC_History13.run, `PV_LIB_SPEC_History13.original, `PV_LIB_SPEC_Builder269.nameKind, `PV_LIB_SPEC_Builder269.sizeKind, `PV_LIB_SPEC_Builder269.builderKind, `PV_LIB_SPEC_Builder269.value, `PV_LIB_SPEC_Builder269.reply, `PV_LIB_SPEC_Builder269.fields, `PV_LIB_SPEC_Builder269.absent, `PV_LIB_SPEC_Builder269.frame, `PV_LIB_SPEC_PrefixNative13.Cut, `PV_LIB_SPEC_PrefixNative13.core, `PV_LIB_SPEC_PrefixNative13.answer, `PV_LIB_SPEC_PrefixNative13.handler, `PV_LIB_SPEC_PrefixNative13.ordinary_framed, `PV_LIB_SPEC_PrefixNative13.transition, `PV_LIB_SPEC_PrefixNative13.control, `PV_LIB_SPEC_PrefixNative13.step, `PV_LIB_SPEC_PrefixNative13.run, `PV_LIB_SPEC_PrefixNative13.actions, `PV_LIB_SPEC_PrefixNative13.preserves_owner_away, `PV_LIB_SPEC_PrefixEnvironment13.native, `PV_LIB_SPEC_PrefixEnvironment13.environment, `PV_LIB_SPEC_PrefixEnvironment13.parameters, `PV_LIB_SPEC_PrefixEnvironment13.pre, `PV_LIB_SPEC_PrefixEnvironment13.allocations, `PV_LIB_SPEC_TlsRecheck13.init, `PV_LIB_SPEC_TlsRecheck13.getter, `PV_LIB_SPEC_TlsRecheck13.config, `PV_LIB_SPEC_TlsRecheck13.getter_selected, `PV_LIB_SPEC_TlsRecheck13.initializer, `PV_LIB_SPEC_TlsRecheck13.getter_value, `PV_LIB_SPEC_TlsRecheck13.getter_reply, `PV_LIB_SPEC_PrefixHistory13.step, `PV_LIB_SPEC_PrefixHistory13.initial, `PV_LIB_SPEC_PrefixHistory13.run, `PV_LIB_SPEC_PrefixHistory13.original])
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
