import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[ `PV_LIB_A_OptionDestruct157, `PV_LIB_A_TypedProgramTable9, `PV_LIB_A_TypedBody218, `PV_LIB_A_TypedBody315, `PV_LIB_A_AllocatorProvenance, `PV_LIB_A_ValueDestruct9, `PV_LIB_A_ProgramBindings9, `PV_LIB_A_GenericDropMachine9, `PV_LIB_A_ProviderAllocator9, `PV_LIB_A_StoreActionTable9, `PV_LIB_A_AllocationBacking9, `PV_LIB_A_WeakOwnerFree9, `PV_LIB_A_ProviderBacking9, `PV_LIB_A_WeakFreeFacts9, `PV_LIB_A_BackingFrame9, `PV_LIB_A_FreeLifetime9, `PV_LIB_A_WeakAllocatorFacts9, `PV_LIB_A_WeakFreeAgreement9, `PV_LIB_A_WeakGuardCaller9, `PV_LIB_A_ThreadInitBacking9],
     #[ `PV_LIB_A_OptionDestruct157.site, `PV_LIB_A_OptionDestruct157.receiver, `PV_LIB_A_OptionDestruct157.payload, `PV_LIB_A_OptionDestruct157.payloadGlue, `PV_LIB_A_OptionDestruct157.finish, `PV_LIB_A_OptionDestruct157.someBranch, `PV_LIB_A_OptionDestruct157.branches, `PV_LIB_A_OptionDestruct157.PV_THR2_LibrarySemantics_OptionDestruct157, `PV_LIB_A_OptionDestruct157.instantiate, `PV_LIB_A_OptionDestruct157.none_branch, `PV_LIB_A_OptionDestruct157.some_branch, `PV_LIB_A_OptionDestruct157.invalid_branch, `PV_LIB_A_OptionDestruct157.exact_type, `PV_LIB_A_TypedProgramTable9.bind, `PV_LIB_A_TypedProgramTable9.selected, `PV_LIB_A_TypedProgramTable9.programs, `PV_LIB_A_TypedProgramTable9.option, `PV_LIB_A_TypedProgramTable9.inherited, `PV_LIB_A_TypedProgramTable9.exact, `PV_LIB_A_TypedProgramTable9.away, `PV_LIB_A_TypedBody218.instantiate, `PV_LIB_A_TypedBody218.program, `PV_LIB_A_TypedBody315.instantiate, `PV_LIB_A_TypedBody315.program, `PV_LIB_A_AllocatorProvenance.globalKind, `PV_LIB_A_AllocatorProvenance.globalType, `PV_LIB_A_AllocatorProvenance.globalValue, `PV_LIB_A_AllocatorProvenance.allocatorType, `PV_LIB_A_AllocatorProvenance.arcAllocator, `PV_LIB_A_AllocatorProvenance.arcGlue, `PV_LIB_A_AllocatorProvenance.arcKind, `PV_LIB_A_AllocatorProvenance.constructed, `PV_LIB_A_AllocatorProvenance.allocator_literal, `PV_LIB_A_AllocatorProvenance.constructor315_moves_A, `PV_LIB_A_AllocatorProvenance.from_inner, `PV_LIB_A_AllocatorProvenance.global_decoded, `PV_LIB_A_AllocatorProvenance.marker_not_default, `PV_LIB_A_AllocatorProvenance.source_allocator, `PV_LIB_A_AllocatorProvenance.source_glue, `PV_LIB_A_ValueDestruct9.resolve, `PV_LIB_A_ValueDestruct9.token, `PV_LIB_A_ValueDestruct9.inherited, `PV_LIB_A_ValueDestruct9.untracked_arc, `PV_LIB_A_ProgramBindings9.PV_THR2_LibrarySemantics_GlobalDestruct228, `PV_LIB_A_ProgramBindings9.bind, `PV_LIB_A_ProgramBindings9.selected, `PV_LIB_A_ProgramBindings9.programs, `PV_LIB_A_ProgramBindings9.option, `PV_LIB_A_ProgramBindings9.allocator_constructor, `PV_LIB_A_ProgramBindings9.global_only, `PV_LIB_A_ProgramBindings9.exact, `PV_LIB_A_GenericDropMachine9.resolution, `PV_LIB_A_GenericDropMachine9.resolution248, `PV_LIB_A_GenericDropMachine9.select248, `PV_LIB_A_GenericDropMachine9.selectCell, `PV_LIB_A_GenericDropMachine9.selectDrop, `PV_LIB_A_GenericDropMachine9.step, `PV_LIB_A_GenericDropMachine9.phase, `PV_LIB_A_GenericDropMachine9.agreement, `PV_LIB_A_ProviderAllocator9.source218_allocator, `PV_LIB_A_ProviderAllocator9.source315_allocator, `PV_LIB_A_ProviderAllocator9.source315_glue, `PV_LIB_StoreActionTable.v2ProvenancePrograms, `PV_LIB_StoreActionTable.v2ProvenanceStep, `PV_LIB_StoreActionTable.provenance_phase, `PV_LIB_StoreActionTable.provenance_agreement, `PV_LIB_StoreActionTable.hooks_tail_bound, `PV_LIB_A_AllocationBacking9.place, `PV_LIB_A_AllocationBacking9.select, `PV_LIB_A_AllocationBacking9.deallocate, `PV_LIB_A_AllocationBacking9.selected, `PV_LIB_A_AllocationBacking9.exact_primitive, `PV_LIB_A_AllocationBacking9.free_lifetime, `PV_LIB_A_AllocationBacking9.no_owned_after_free, `PV_LIB_A_AllocationBacking9.unregistered, `PV_LIB_A_WeakOwnerFree9.globalType, `PV_LIB_A_WeakOwnerFree9.allocator, `PV_LIB_A_WeakOwnerFree9.weakAllocator, `PV_LIB_A_WeakOwnerFree9.reply, `PV_LIB_A_WeakOwnerFree9.gap, `PV_LIB_A_WeakOwnerFree9.poll, `PV_LIB_A_WeakOwnerFree9.step, `PV_LIB_A_WeakOwnerFree9.pending_reply, `PV_LIB_A_WeakOwnerFree9.retry, `PV_LIB_A_WeakOwnerFree9.reply_effects, `PV_LIB_A_ProviderBacking9.same_place, `PV_LIB_A_ProviderBacking9.successful_backing, `PV_LIB_A_ProviderBacking9.matching_free, `PV_LIB_A_WeakFreeFacts9.poll_graph, `PV_LIB_A_WeakFreeFacts9.pending, `PV_LIB_A_WeakFreeFacts9.success, `PV_LIB_A_WeakFreeFacts9.non_success_source, `PV_LIB_A_WeakFreeFacts9.erased_allocator, `PV_LIB_A_BackingFrame9.native, `PV_LIB_A_BackingFrame9.newer_registration, `PV_LIB_A_BackingFrame9.free_registry, `PV_LIB_A_FreeLifetime9.old_world_unchanged, `PV_LIB_A_FreeLifetime9.primitive_success, `PV_LIB_A_FreeLifetime9.primitive_non_success, `PV_LIB_A_WeakAllocatorFacts9.direct, `PV_LIB_A_WeakAllocatorFacts9.borrowed, `PV_LIB_A_WeakAllocatorFacts9.guard_from_arc, `PV_LIB_A_WeakFreeAgreement9.Neutral, `PV_LIB_A_WeakFreeAgreement9.agreement, `PV_LIB_A_WeakGuardCaller9.allocator, `PV_LIB_A_ThreadInitBacking9.registration])
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
