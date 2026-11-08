import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_A_StoreActionMachine, `PV_LIB_A_StoreActionTable, `PV_LIB_A_StoreActionTable10, `PV_LIB_A_StoreActionTable11, `PV_LIB_A_StoreActionTable12, `PV_LIB_A_StoreActionTable13, `PV_LIB_A_StoreActionTable7, `PV_LIB_A_StoreActionTable8, `PV_LIB_A_StoreActionTable9, `PV_LIB_SpawnNative, `PV_LIB_Thread164, `PV_LIB_Thread218, `PV_LIB_Thread315, `PV_LIB_ThreadInstances, `PV_LIB_ThreadNamed, `PV_LIB_TlsNative, `PV_LIB_VecNew, `PV_W1_BoxEffects, `PV_W1_ClosedLeaves]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SpawnNative.law453, `PV_LIB_SpawnNative.law454, `PV_LIB_SpawnNative.law455, `PV_LIB_SpawnNative.law456, `PV_LIB_SpawnNative.law457, `PV_LIB_SpawnNative.law459, `PV_LIB_SpawnNative.model213, `PV_LIB_SpawnNative.model295, `PV_LIB_SpawnNative.model452, `PV_LIB_SpawnNative.model453, `PV_LIB_SpawnNative.model454, `PV_LIB_SpawnNative.model455, `PV_LIB_SpawnNative.model456, `PV_LIB_SpawnNative.model457, `PV_LIB_SpawnNative.model459, `PV_LIB_StoreActionTable.advance_agreement, `PV_LIB_StoreActionTable.agreement, `PV_LIB_StoreActionTable.clone_all_answers, `PV_LIB_StoreActionTable.coverage, `PV_LIB_StoreActionTable.deliver, `PV_LIB_StoreActionTable.destruction_agreement10, `PV_LIB_StoreActionTable.effects, `PV_LIB_StoreActionTable.hooks_tail_bound, `PV_LIB_StoreActionTable.interpret, `PV_LIB_StoreActionTable.native, `PV_LIB_StoreActionTable.originalDestructionCarrier10, `PV_LIB_StoreActionTable.prefix_step11, `PV_LIB_StoreActionTable.prefix_step12, `PV_LIB_StoreActionTable.prefix_step13, `PV_LIB_StoreActionTable.provenance_agreement, `PV_LIB_StoreActionTable.provenance_phase, `PV_LIB_StoreActionTable.scope_overflow, `PV_LIB_StoreActionTable.select, `PV_LIB_StoreActionTable.sourceBegin, `PV_LIB_StoreActionTable.sourceCoverage, `PV_LIB_StoreActionTable.sourceReceive, `PV_LIB_StoreActionTable.sourceSelect, `PV_LIB_StoreActionTable.sourceStep, `PV_LIB_StoreActionTable.source_agreement, `PV_LIB_StoreActionTable.source_done_reply, `PV_LIB_StoreActionTable.source_native, `PV_LIB_StoreActionTable.source_pending, `PV_LIB_StoreActionTable.start, `PV_LIB_StoreActionTable.step, `PV_LIB_StoreActionTable.strong_cas, `PV_LIB_StoreActionTable.typed_agreement, `PV_LIB_StoreActionTable.typed_phase, `PV_LIB_StoreActionTable.v2, `PV_LIB_StoreActionTable.v2DestructionEntry10, `PV_LIB_StoreActionTable.v2DestructionPrograms10, `PV_LIB_StoreActionTable.v2DestructionStep10, `PV_LIB_StoreActionTable.v2PrefixAdvance11, `PV_LIB_StoreActionTable.v2PrefixAdvance12, `PV_LIB_StoreActionTable.v2PrefixAdvance13, `PV_LIB_StoreActionTable.v2PrefixEntry11, `PV_LIB_StoreActionTable.v2PrefixEntry12, `PV_LIB_StoreActionTable.v2PrefixStep11, `PV_LIB_StoreActionTable.v2PrefixStep12, `PV_LIB_StoreActionTable.v2PrefixStep13, `PV_LIB_StoreActionTable.v2ProvenancePrograms, `PV_LIB_StoreActionTable.v2ProvenanceStep, `PV_LIB_StoreActionTable.v2Source, `PV_LIB_StoreActionTable.v2TypedPrograms, `PV_LIB_StoreActionTable.v2TypedStep]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_StoreActionTable.weak_cas, `PV_LIB_Thread164.installed, `PV_LIB_Thread218.installed, `PV_LIB_Thread315.installed, `PV_LIB_ThreadInstances.installed126, `PV_LIB_ThreadInstances.installed218, `PV_LIB_ThreadInstances.installed222, `PV_LIB_ThreadInstances.installed315, `PV_LIB_ThreadInstances.law126, `PV_LIB_ThreadInstances.law218, `PV_LIB_ThreadInstances.law222, `PV_LIB_ThreadInstances.law315, `PV_LIB_ThreadInstances.model126, `PV_LIB_ThreadInstances.model218, `PV_LIB_ThreadInstances.model222, `PV_LIB_ThreadInstances.model315, `PV_LIB_ThreadNamed.certified123, `PV_LIB_ThreadNamed.certified18, `PV_LIB_ThreadNamed.certified468, `PV_LIB_ThreadNamed.certified469, `PV_LIB_ThreadNamed.law123, `PV_LIB_ThreadNamed.law18, `PV_LIB_ThreadNamed.law468, `PV_LIB_ThreadNamed.law469, `PV_LIB_ThreadNamed.model123, `PV_LIB_ThreadNamed.model18, `PV_LIB_ThreadNamed.model468, `PV_LIB_ThreadNamed.model469, `PV_LIB_TlsNative.certified11, `PV_LIB_TlsNative.certified122, `PV_LIB_TlsNative.certified127, `PV_LIB_TlsNative.certified128, `PV_LIB_TlsNative.certified129, `PV_LIB_TlsNative.certified130, `PV_LIB_TlsNative.certified319, `PV_LIB_TlsNative.certified410, `PV_LIB_TlsNative.law11, `PV_LIB_TlsNative.law122, `PV_LIB_TlsNative.law127, `PV_LIB_TlsNative.law128, `PV_LIB_TlsNative.law129, `PV_LIB_TlsNative.law130, `PV_LIB_TlsNative.law319, `PV_LIB_TlsNative.law410, `PV_LIB_TlsNative.model11, `PV_LIB_TlsNative.model122, `PV_LIB_TlsNative.model127, `PV_LIB_TlsNative.model128, `PV_LIB_TlsNative.model129, `PV_LIB_TlsNative.model130, `PV_LIB_TlsNative.model319, `PV_LIB_TlsNative.model410, `PV_LIB_VecNew.installed, `PV_LIB_VecNew.law, `PV_W1_BoxEffects.contract, `PV_W1_ClosedLeaves.f121, `PV_W1_ClosedLeaves.f123, `PV_W1_ClosedLeaves.f134, `PV_W1_ClosedLeaves.f18, `PV_W1_ClosedLeaves.f214, `PV_W1_ClosedLeaves.f217]
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
