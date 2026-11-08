import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_W1_ClosedLeaves, `PV_W1_DropLeaf, `PV_W1_NativeLeaves, `PV_W1_TLSLeaves, `PV_W5_AllocatorContracts, `PV_W5_CopyContract, `PV_W5_DropLeaf, `PV_W5_NativeLeaves, `PV_W5_NoAllocShim, `PV_W5_PtrFromParts]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_W1_ClosedLeaves.f312, `PV_W1_ClosedLeaves.f313, `PV_W1_ClosedLeaves.f320, `PV_W1_ClosedLeaves.f344, `PV_W1_DropLeaf.contract, `PV_W1_NativeLeaves.f11, `PV_W1_NativeLeaves.f122, `PV_W1_NativeLeaves.f127, `PV_W1_NativeLeaves.f128, `PV_W1_NativeLeaves.f129, `PV_W1_NativeLeaves.f130, `PV_W1_NativeLeaves.f14, `PV_W1_NativeLeaves.f165, `PV_W1_NativeLeaves.f168, `PV_W1_NativeLeaves.f171, `PV_W1_NativeLeaves.f213, `PV_W1_NativeLeaves.f268, `PV_W1_NativeLeaves.f269, `PV_W1_NativeLeaves.f271, `PV_W1_NativeLeaves.f295, `PV_W1_NativeLeaves.f3, `PV_W1_NativeLeaves.f319, `PV_W1_NativeLeaves.f360, `PV_W1_NativeLeaves.f4, `PV_W1_NativeLeaves.f410, `PV_W1_NativeLeaves.f452, `PV_W1_NativeLeaves.f453, `PV_W1_NativeLeaves.f454, `PV_W1_NativeLeaves.f455, `PV_W1_NativeLeaves.f456, `PV_W1_NativeLeaves.f457, `PV_W1_NativeLeaves.f459, `PV_W1_NativeLeaves.f7, `PV_W1_NativeLeaves.f8, `PV_W1_TLSLeaves.f468, `PV_W1_TLSLeaves.f469, `PV_W5_AllocatorContracts.malloc, `PV_W5_AllocatorContracts.zeroed, `PV_W5_CopyContract.contract, `PV_W5_DropLeaf.contract, `PV_W5_NativeLeaves.arrayRepeat, `PV_W5_NativeLeaves.arrayToSliceMut, `PV_W5_NativeLeaves.arrayToSliceShared, `PV_W5_NativeLeaves.f10, `PV_W5_NativeLeaves.f16, `PV_W5_NativeLeaves.f17, `PV_W5_NativeLeaves.f18, `PV_W5_NativeLeaves.f20, `PV_W5_NativeLeaves.f36, `PV_W5_NativeLeaves.f37, `PV_W5_NativeLeaves.f38, `PV_W5_NativeLeaves.f46, `PV_W5_NativeLeaves.f62, `PV_W5_NativeLeaves.indexMut, `PV_W5_NoAllocShim.contract, `PV_W5_PtrFromParts.mut_contract, `PV_W5_PtrFromParts.shared_contract]
@[noinline] private def v1Roots : Array Name := v1Roots0
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
