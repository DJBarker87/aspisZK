import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_OptionDestruct157, `PV_LIB_A_OwnerStore, `PV_LIB_A_OwnerStoreActions, `PV_LIB_A_OwnerStoreTransport, `PV_LIB_A_OwnerStoreV2, `PV_LIB_A_OwnerStoreV3, `PV_LIB_A_OwnerTableCongruence14, `PV_LIB_A_Payload24810, `PV_LIB_A_Post93Prefix12, `PV_LIB_A_PreActionTraceV2, `PV_LIB_A_PreActionTraceV3, `PV_LIB_A_PrefixComposition14, `PV_LIB_A_PrefixMachine11, `PV_LIB_A_PrefixNativeCalls14, `PV_LIB_A_PrefixSequenceFrames14, `PV_LIB_A_PrefixStructuredCalls14, `PV_LIB_A_PrefixTransport, `PV_LIB_A_ProgramBindings9, `PV_LIB_A_ProviderAllocator9, `PV_LIB_A_ProviderBacking9, `PV_LIB_A_PureCalls]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_A_OptionDestruct157.exact_type, `PV_LIB_A_OptionDestruct157.finish, `PV_LIB_A_OptionDestruct157.instantiate, `PV_LIB_A_OptionDestruct157.invalid_branch, `PV_LIB_A_OptionDestruct157.none_branch, `PV_LIB_A_OptionDestruct157.payload, `PV_LIB_A_OptionDestruct157.payloadGlue, `PV_LIB_A_OptionDestruct157.receiver, `PV_LIB_A_OptionDestruct157.site, `PV_LIB_A_OptionDestruct157.someBranch, `PV_LIB_A_OptionDestruct157.some_branch, `PV_LIB_A_OwnerStore.agreement, `PV_LIB_A_OwnerStore.effects, `PV_LIB_A_OwnerStore.installed, `PV_LIB_A_OwnerStoreActions.completed, `PV_LIB_A_OwnerStoreActions.nonwaiting, `PV_LIB_A_OwnerStoreTransport.advance_add, `PV_LIB_A_OwnerStoreTransport.advance_agreement, `PV_LIB_A_OwnerStoreTransport.registry, `PV_LIB_A_OwnerStoreTransport.segment, `PV_LIB_A_OwnerStoreV2.advance_agreement, `PV_LIB_A_OwnerStoreV2.agreement, `PV_LIB_A_OwnerStoreV2.effects, `PV_LIB_A_OwnerStoreV3.advance_agreement, `PV_LIB_A_OwnerStoreV3.agreement, `PV_LIB_A_OwnerStoreV3.effects, `PV_LIB_A_OwnerTableCongruence14.operator, `PV_LIB_A_OwnerTableCongruence14.owner, `PV_LIB_A_OwnerTableCongruence14.uniform, `PV_LIB_A_Payload24810.hooks_resolution, `PV_LIB_A_Payload24810.hooks_selected, `PV_LIB_A_Payload24810.source, `PV_LIB_A_Post93Prefix12.after, `PV_LIB_A_Post93Prefix12.aggregateAfter, `PV_LIB_A_Post93Prefix12.retained, `PV_LIB_A_Post93Prefix12.run, `PV_LIB_A_Post93Prefix12.spawnAfter, `PV_LIB_A_Post93Prefix12.steps, `PV_LIB_A_PreActionTraceV2.append, `PV_LIB_A_PreActionTraceV2.nonwaiting, `PV_LIB_A_PreActionTraceV2.run, `PV_LIB_A_PreActionTraceV2.step, `PV_LIB_A_PreActionTraceV3.append, `PV_LIB_A_PreActionTraceV3.nonwaiting, `PV_LIB_A_PreActionTraceV3.run, `PV_LIB_A_PreActionTraceV3.step, `PV_LIB_A_PrefixComposition14.chain, `PV_LIB_A_PrefixComposition14.chained, `PV_LIB_A_PrefixComposition14.join, `PV_LIB_A_PrefixComposition14.joined, `PV_LIB_A_PrefixComposition14.lift, `PV_LIB_A_PrefixComposition14.lifted, `PV_LIB_A_PrefixMachine11.advance_add, `PV_LIB_A_PrefixMachine11.append, `PV_LIB_A_PrefixMachine11.run, `PV_LIB_A_PrefixMachine11.step, `PV_LIB_A_PrefixNativeCalls14.child121, `PV_LIB_A_PrefixNativeCalls14.child122, `PV_LIB_A_PrefixNativeCalls14.child123, `PV_LIB_A_PrefixNativeCalls14.child124, `PV_LIB_A_PrefixNativeCalls14.child134, `PV_LIB_A_PrefixNativeCalls14.child410, `PV_LIB_A_PrefixNativeCalls14.run121, `PV_LIB_A_PrefixNativeCalls14.run122]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_A_PrefixNativeCalls14.run123, `PV_LIB_A_PrefixNativeCalls14.run124, `PV_LIB_A_PrefixNativeCalls14.run134, `PV_LIB_A_PrefixNativeCalls14.run410, `PV_LIB_A_PrefixNativeCalls14.shape121, `PV_LIB_A_PrefixNativeCalls14.shape122, `PV_LIB_A_PrefixNativeCalls14.shape123, `PV_LIB_A_PrefixNativeCalls14.shape124, `PV_LIB_A_PrefixNativeCalls14.shape134, `PV_LIB_A_PrefixNativeCalls14.shape410, `PV_LIB_A_PrefixSequenceFrames14.iterator, `PV_LIB_A_PrefixSequenceFrames14.safe0, `PV_LIB_A_PrefixSequenceFrames14.safe1, `PV_LIB_A_PrefixSequenceFrames14.safe10, `PV_LIB_A_PrefixSequenceFrames14.safe11, `PV_LIB_A_PrefixSequenceFrames14.safe12, `PV_LIB_A_PrefixSequenceFrames14.safe2, `PV_LIB_A_PrefixSequenceFrames14.safe3, `PV_LIB_A_PrefixSequenceFrames14.safe4, `PV_LIB_A_PrefixSequenceFrames14.safe5, `PV_LIB_A_PrefixSequenceFrames14.safe6, `PV_LIB_A_PrefixSequenceFrames14.safe7, `PV_LIB_A_PrefixSequenceFrames14.safe8, `PV_LIB_A_PrefixSequenceFrames14.safe9, `PV_LIB_A_PrefixStructuredCalls14.lookup125, `PV_LIB_A_PrefixStructuredCalls14.lookup15, `PV_LIB_A_PrefixStructuredCalls14.lookup208, `PV_LIB_A_PrefixStructuredCalls14.lookup219, `PV_LIB_A_PrefixStructuredCalls14.lookup220, `PV_LIB_A_PrefixStructuredCalls14.run125, `PV_LIB_A_PrefixStructuredCalls14.run15, `PV_LIB_A_PrefixStructuredCalls14.run208, `PV_LIB_A_PrefixStructuredCalls14.run219, `PV_LIB_A_PrefixStructuredCalls14.run220, `PV_LIB_A_PrefixStructuredCalls14.shape125, `PV_LIB_A_PrefixStructuredCalls14.shape15, `PV_LIB_A_PrefixStructuredCalls14.shape208, `PV_LIB_A_PrefixStructuredCalls14.shape219, `PV_LIB_A_PrefixStructuredCalls14.shape220, `PV_LIB_A_PrefixTransport.prefix_identity, `PV_LIB_A_ProgramBindings9.PV_THR2_LibrarySemantics_GlobalDestruct228, `PV_LIB_A_ProgramBindings9.allocator_constructor, `PV_LIB_A_ProgramBindings9.bind, `PV_LIB_A_ProgramBindings9.exact, `PV_LIB_A_ProgramBindings9.global_only, `PV_LIB_A_ProgramBindings9.option, `PV_LIB_A_ProgramBindings9.programs, `PV_LIB_A_ProgramBindings9.selected, `PV_LIB_A_ProviderAllocator9.source218_allocator, `PV_LIB_A_ProviderAllocator9.source315_allocator, `PV_LIB_A_ProviderAllocator9.source315_glue, `PV_LIB_A_ProviderBacking9.matching_free, `PV_LIB_A_ProviderBacking9.same_place, `PV_LIB_A_ProviderBacking9.successful_backing, `PV_LIB_A_PureCalls.asRef_source_local, `PV_LIB_A_PureCalls.certified277, `PV_LIB_A_PureCalls.certified278, `PV_LIB_A_PureCalls.certified279, `PV_LIB_A_PureCalls.certified280, `PV_LIB_A_PureCalls.delivered_value, `PV_LIB_A_PureCalls.worlds]
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
