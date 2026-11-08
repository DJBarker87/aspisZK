import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[ `PV_LIB_A_DropMetadata, `PV_LIB_A_TypedDestruct, `PV_LIB_A_DestructMethods, `PV_LIB_A_TypedBody608, `PV_LIB_A_TypedBody661, `PV_LIB_A_TypedBody486, `PV_LIB_A_TypedBody584, `PV_LIB_A_ExactDestructMethods, `PV_LIB_A_DropInPlace248, `PV_LIB_A_GenericDropBinding, `PV_LIB_A_CellDestruct504, `PV_LIB_A_GenericDropMachine, `PV_LIB_A_TypedBindingFacts, `PV_LIB_A_CellDestructFacts, `PV_LIB_A_DestructionNumbering, `PV_LIB_A_TypedBody405, `PV_LIB_A_TypedBody222, `PV_LIB_A_UnwindMatch, `PV_LIB_A_UnwindMatchCorrectness, `PV_LIB_A_LoweredBody644, `PV_LIB_A_LoweredBody454, `PV_LIB_A_TypedProgramTable8, `PV_LIB_A_StoreActionTable8, `PV_LIB_A_SpawnHooksTailGap, `PV_LIB_A_UnwindReplies],
     #[ `PV_LIB_A_DropMetadata.lookup, `PV_LIB_A_TypedDestruct.normalize, `PV_LIB_A_TypedDestruct.substitute, `PV_LIB_A_TypedDestruct.generics, `PV_LIB_A_TypedDestruct.encode, `PV_LIB_A_TypedDestruct.fnPtr, `PV_LIB_A_TypedDestruct.substitute_type, `PV_LIB_A_TypedDestruct.preserves_atom, `PV_LIB_A_TypedDestruct.generics_roundtrip, `PV_LIB_A_DestructMethods.implementation, `PV_LIB_A_DestructMethods.adtImpl, `PV_LIB_A_DestructMethods.concrete, `PV_LIB_A_DestructMethods.byType, `PV_LIB_A_DestructMethods.resolve, `PV_LIB_A_DestructMethods.concrete_shape, `PV_LIB_A_TypedBody608.instantiate, `PV_LIB_A_TypedBody608.program, `PV_LIB_A_TypedBody661.instantiate, `PV_LIB_A_TypedBody661.program, `PV_LIB_A_TypedBody486.instantiate, `PV_LIB_A_TypedBody486.program, `PV_LIB_A_TypedBody584.instantiate, `PV_LIB_A_TypedBody584.program, `PV_LIB_A_ExactDestructMethods.implementation, `PV_LIB_A_ExactDestructMethods.adtImpl, `PV_LIB_A_ExactDestructMethods.concrete, `PV_LIB_A_ExactDestructMethods.byType, `PV_LIB_A_ExactDestructMethods.resolve, `PV_LIB_A_ExactDestructMethods.method_types, `PV_LIB_A_ExactDestructMethods.methodGenerics, `PV_LIB_A_DropInPlace248.forwardedWait, `PV_LIB_A_DropInPlace248.resolution, `PV_LIB_A_DropInPlace248.select, `PV_LIB_A_DropInPlace248.PV_THR2_LibrarySemantics_DropInPlace248, `PV_LIB_A_DropInPlace248.forwarded, `PV_LIB_A_DropInPlace248.frame, `PV_LIB_A_GenericDropBinding.normalized, `PV_LIB_A_GenericDropBinding.resolveToken, `PV_LIB_A_GenericDropBinding.bind, `PV_LIB_A_GenericDropBinding.selected, `PV_LIB_A_GenericDropBinding.programs, `PV_LIB_A_GenericDropBinding.arc, `PV_LIB_A_GenericDropBinding.slow, `PV_LIB_A_GenericDropBinding.weakGuard, `PV_LIB_A_GenericDropBinding.hooks, `PV_LIB_A_GenericDropBinding.exact, `PV_LIB_A_GenericDropBinding.away, `PV_LIB_A_CellDestruct504.site, `PV_LIB_A_CellDestruct504.suffix, `PV_LIB_A_CellDestruct504.select, `PV_LIB_A_CellDestruct504.enter, `PV_LIB_A_CellDestruct504.enter_frame, `PV_LIB_A_CellDestruct504.call_suffix, `PV_LIB_A_CellDestruct504.noop_invalidates, `PV_LIB_A_GenericDropMachine.unitTag, `PV_LIB_A_GenericDropMachine.selectDrop, `PV_LIB_A_GenericDropMachine.noop, `PV_LIB_A_GenericDropMachine.step, `PV_LIB_A_GenericDropMachine.phase, `PV_LIB_A_GenericDropMachine.agreement, `PV_LIB_A_TypedBindingFacts.empty, `PV_LIB_A_TypedBindingFacts.hooksType, `PV_LIB_A_TypedBindingFacts.arcType, `PV_LIB_A_TypedBindingFacts.untracked, `PV_LIB_A_TypedBindingFacts.hooks_method, `PV_LIB_A_TypedBindingFacts.typed248_hooks, `PV_LIB_A_TypedBindingFacts.arc_allocator_unbound, `PV_LIB_A_TypedBindingFacts.no_selected_arc_glue, `PV_LIB_A_TypedBindingFacts.erased_allocator_not_noop, `PV_LIB_A_TypedBindingFacts.slow_specialized, `PV_LIB_A_CellDestructFacts.selected_from_source, `PV_LIB_A_CellDestructFacts.emitted602, `PV_LIB_A_CellDestructFacts.saved_old, `PV_LIB_A_CellDestructFacts.away_holder, `PV_LIB_A_DestructionNumbering.cell_entry, `PV_LIB_A_DestructionNumbering.drop_entry, `PV_LIB_A_TypedBody405.instantiate, `PV_LIB_A_TypedBody405.program, `PV_LIB_A_TypedBody222.instantiate, `PV_LIB_A_TypedBody222.program, `PV_LIB_A_UnwindMatch.variantKey, `PV_LIB_A_UnwindMatch.invalidKey, `PV_LIB_A_UnwindMatch.gapOperator, `PV_LIB_A_UnwindMatch.key, `PV_LIB_A_UnwindMatch.operation, `PV_LIB_A_UnwindMatch.carrier, `PV_LIB_A_UnwindMatch.gap, `PV_LIB_A_UnwindMatch.arms, `PV_LIB_A_UnwindMatch.otherwise, `PV_LIB_A_UnwindMatch.variant_key, `PV_LIB_A_UnwindMatch.invalid_key, `PV_LIB_A_UnwindMatch.gap_operator, `PV_LIB_A_UnwindMatch.fields, `PV_LIB_A_UnwindMatchCorrectness.selectArm, `PV_LIB_A_UnwindMatchCorrectness.source_selector, `PV_LIB_A_UnwindMatchCorrectness.keys, `PV_LIB_A_UnwindMatchCorrectness.variants, `PV_LIB_A_UnwindMatchCorrectness.selection, `PV_LIB_A_UnwindMatchCorrectness.gap_is_undefined, `PV_LIB_A_LoweredBody644.instantiate, `PV_LIB_A_LoweredBody644.program, `PV_LIB_A_LoweredBody454.instantiate, `PV_LIB_A_LoweredBody454.program, `PV_LIB_A_TypedProgramTable8.bind, `PV_LIB_A_TypedProgramTable8.selected, `PV_LIB_A_TypedProgramTable8.programs, `PV_LIB_A_TypedProgramTable8.arc_glue, `PV_LIB_A_TypedProgramTable8.inner, `PV_LIB_A_TypedProgramTable8.hooks_drop, `PV_LIB_A_TypedProgramTable8.run_hooks, `PV_LIB_A_TypedProgramTable8.exact, `PV_LIB_A_TypedProgramTable8.away, `PV_LIB_StoreActionTable.v2TypedPrograms, `PV_LIB_StoreActionTable.v2TypedStep, `PV_LIB_StoreActionTable.typed_phase, `PV_LIB_StoreActionTable.typed_agreement, `PV_LIB_A_SpawnHooksTailGap.actual_tail, `PV_LIB_A_SpawnHooksTailGap.option_source_unbound, `PV_LIB_A_SpawnHooksTailGap.no_option_body, `PV_LIB_A_SpawnHooksTailGap.actual_arc_cleanup, `PV_LIB_A_UnwindReplies.read_fields, `PV_LIB_A_UnwindReplies.replace_fields, `PV_LIB_A_UnwindReplies.read_address, `PV_LIB_A_UnwindReplies.write_address, `PV_LIB_A_UnwindReplies.read_place, `PV_LIB_A_UnwindReplies.locate_place, `PV_LIB_A_UnwindReplies.store_result, `PV_LIB_A_UnwindReplies.full_reply])
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
        for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk] do
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
