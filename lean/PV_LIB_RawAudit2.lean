import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_Arc124, `PV_LIB_Arc124Allocated, `PV_LIB_Arc124Counts, `PV_LIB_ArcClone360, `PV_LIB_Atomic121, `PV_LIB_Box443, `PV_LIB_Box458, `PV_LIB_Box537, `PV_LIB_BoxNew, `PV_LIB_Clone214, `PV_LIB_Drop, `PV_LIB_NativeGraph, `PV_LIB_Registry, `PV_LIB_RootNative, `PV_LIB_ScopeNative, `PV_LIB_SliceAlloc47, `PV_LIB_SliceAlloc48, `PV_LIB_SliceAlloc59, `PV_LIB_SliceAllocNative, `PV_LIB_SliceAllocators, `PV_LIB_SliceBuiltinNative, `PV_LIB_SliceCopy, `PV_LIB_SliceCtor31, `PV_LIB_SliceCtor35, `PV_LIB_SliceDrop, `PV_LIB_SliceLoopNative, `PV_LIB_SliceNativeGraph, `PV_LIB_SliceNoAlloc, `PV_LIB_SlicePtrParts, `PV_LIB_SourceStoreComparison, `PV_LIB_SpawnNative, `PV_LIB_ThreadNamed, `PV_LIB_TlsNative],
     #[`PV_LIB_Arc124.installed, `PV_LIB_Arc124.internal_reached, `PV_LIB_Arc124Allocated.reached, `PV_LIB_Arc124Counts.certified, `PV_LIB_ArcClone360.certified, `PV_LIB_Atomic121.certified, `PV_LIB_Atomic121.returned_value, `PV_LIB_Box443.installed, `PV_LIB_Box443.internal_reached, `PV_LIB_Box458.certified, `PV_LIB_Box458.installed, `PV_LIB_Box458.internal_reached, `PV_LIB_Box537.installed, `PV_LIB_Box537.internal_reached, `PV_LIB_BoxNew.certified, `PV_LIB_Clone214.certified, `PV_LIB_Drop.certified, `PV_LIB_NativeGraph.certified, `PV_LIB_Registry.certified, `PV_LIB_RootNative.certified171, `PV_LIB_RootNative.certified268, `PV_LIB_RootNative.certified3, `PV_LIB_RootNative.certified4, `PV_LIB_ScopeNative.certified14, `PV_LIB_ScopeNative.certified165, `PV_LIB_ScopeNative.certified168, `PV_LIB_ScopeNative.certified269, `PV_LIB_ScopeNative.certified271, `PV_LIB_ScopeNative.certified7, `PV_LIB_ScopeNative.certified8, `PV_LIB_SliceAlloc47.certified, `PV_LIB_SliceAlloc48.certified, `PV_LIB_SliceAlloc59.certified, `PV_LIB_SliceAllocNative.certified_f36, `PV_LIB_SliceAllocNative.certified_f37, `PV_LIB_SliceAllocNative.certified_f38, `PV_LIB_SliceAllocNative.certified_f46, `PV_LIB_SliceAllocNative.certified_f62, `PV_LIB_SliceAllocators.certified64, `PV_LIB_SliceAllocators.certified65, `PV_LIB_SliceBuiltinNative.certified_arrayRepeat, `PV_LIB_SliceBuiltinNative.certified_arrayToSliceMut, `PV_LIB_SliceBuiltinNative.certified_arrayToSliceShared, `PV_LIB_SliceBuiltinNative.certified_indexMut, `PV_LIB_SliceCopy.certified, `PV_LIB_SliceCtor31.certified, `PV_LIB_SliceCtor35.certified, `PV_LIB_SliceDrop.certified, `PV_LIB_SliceLoopNative.certified_f10, `PV_LIB_SliceLoopNative.certified_f16, `PV_LIB_SliceLoopNative.certified_f17, `PV_LIB_SliceLoopNative.certified_f18, `PV_LIB_SliceLoopNative.certified_f20, `PV_LIB_SliceNativeGraph.internalModel, `PV_LIB_SliceNativeGraph.model, `PV_LIB_SliceNoAlloc.certified, `PV_LIB_SlicePtrParts.certifiedMut, `PV_LIB_SlicePtrParts.certifiedShared, `PV_LIB_SourceStoreComparison.cell_gap, `PV_LIB_SourceStoreComparison.public_gap, `PV_LIB_SourceStoreComparison.running_cell, `PV_LIB_SpawnNative.certified213, `PV_LIB_SpawnNative.certified295, `PV_LIB_SpawnNative.certified452, `PV_LIB_SpawnNative.certified453, `PV_LIB_SpawnNative.certified454, `PV_LIB_SpawnNative.certified455, `PV_LIB_SpawnNative.certified456, `PV_LIB_SpawnNative.certified457, `PV_LIB_SpawnNative.certified459, `PV_LIB_ThreadNamed.certified123, `PV_LIB_ThreadNamed.certified18, `PV_LIB_ThreadNamed.certified468, `PV_LIB_ThreadNamed.certified469, `PV_LIB_TlsNative.certified11, `PV_LIB_TlsNative.certified122, `PV_LIB_TlsNative.certified127, `PV_LIB_TlsNative.certified128, `PV_LIB_TlsNative.certified129, `PV_LIB_TlsNative.certified130, `PV_LIB_TlsNative.certified319, `PV_LIB_TlsNative.certified410])
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
