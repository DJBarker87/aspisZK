import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    (#[`PV_LIB_SPEC_RebasedCaptures18, `PV_LIB_SPEC_RebasedEntry18, `PV_LIB_SPEC_RebasedPre18, `PV_LIB_SPEC_DisjointCaptures18, `PV_LIB_SPEC_DisjointEntry18, `PV_LIB_SPEC_DisjointPre18, `PV_LIB_SPEC_EntryWorld18, `PV_LIB_SPEC_Prefix54World18, `PV_LIB_SPEC_TlsWorld18_1, `PV_LIB_SPEC_TlsWorld18_2, `PV_LIB_SPEC_TlsWorld18_3, `PV_LIB_SPEC_TlsWorld18_4, `PV_LIB_SPEC_TlsWorld18_5, `PV_LIB_SPEC_History18],
     #[`PV_LIB_SPEC_RebasedCaptures18.site, `PV_LIB_SPEC_RebasedCaptures18.zero, `PV_LIB_SPEC_RebasedCaptures18.one, `PV_LIB_SPEC_RebasedCaptures18.captures, `PV_LIB_SPEC_RebasedCaptures18.places, `PV_LIB_SPEC_RebasedCaptures18.runHeader, `PV_LIB_SPEC_RebasedCaptures18.nHeader, `PV_LIB_SPEC_RebasedCaptures18.fHeader, `PV_LIB_SPEC_RebasedCaptures18.taskHeader, `PV_LIB_SPEC_RebasedCaptures18.bytes, `PV_LIB_SPEC_RebasedCaptures18.state, `PV_LIB_SPEC_RebasedCaptures18.receivers, `PV_LIB_SPEC_RebasedCaptures18.run_bytes, `PV_LIB_SPEC_RebasedCaptures18.n_bytes, `PV_LIB_SPEC_RebasedCaptures18.run_typed, `PV_LIB_SPEC_RebasedCaptures18.n_typed, `PV_LIB_SPEC_RebasedCaptures18.f_typed, `PV_LIB_SPEC_RebasedCaptures18.tasks_typed, `PV_LIB_SPEC_RebasedCaptures18.closure, `PV_LIB_SPEC_RebasedCaptures18.entry_nonempty, `PV_LIB_SPEC_RebasedEntry18.slot, `PV_LIB_SPEC_RebasedEntry18.store, `PV_LIB_SPEC_RebasedEntry18.tlsState, `PV_LIB_SPEC_RebasedEntry18.hooksSlot, `PV_LIB_SPEC_RebasedEntry18.state, `PV_LIB_SPEC_RebasedEntry18.input, `PV_LIB_SPEC_RebasedEntry18.memory_before, `PV_LIB_SPEC_RebasedPre18.memory_before, `PV_LIB_SPEC_RebasedPre18.receivers, `PV_LIB_SPEC_RebasedPre18.run_bytes, `PV_LIB_SPEC_RebasedPre18.n_bytes, `PV_LIB_SPEC_RebasedPre18.run_typed, `PV_LIB_SPEC_RebasedPre18.n_typed, `PV_LIB_SPEC_RebasedPre18.f_typed, `PV_LIB_SPEC_RebasedPre18.tasks_typed, `PV_LIB_SPEC_RebasedPre18.fresh, `PV_LIB_SPEC_RebasedPre18.validity, `PV_LIB_SPEC_RebasedPre18.owner, `PV_LIB_SPEC_RebasedPre18.captured, `PV_LIB_SPEC_RebasedPre18.pre, `PV_LIB_SPEC_DisjointCaptures18.site, `PV_LIB_SPEC_DisjointCaptures18.zero, `PV_LIB_SPEC_DisjointCaptures18.one, `PV_LIB_SPEC_DisjointCaptures18.captures, `PV_LIB_SPEC_DisjointCaptures18.places, `PV_LIB_SPEC_DisjointCaptures18.runHeader, `PV_LIB_SPEC_DisjointCaptures18.nHeader, `PV_LIB_SPEC_DisjointCaptures18.fHeader, `PV_LIB_SPEC_DisjointCaptures18.taskHeader, `PV_LIB_SPEC_DisjointCaptures18.bytes, `PV_LIB_SPEC_DisjointCaptures18.state, `PV_LIB_SPEC_DisjointCaptures18.receivers, `PV_LIB_SPEC_DisjointCaptures18.run_bytes, `PV_LIB_SPEC_DisjointCaptures18.n_bytes, `PV_LIB_SPEC_DisjointCaptures18.run_typed, `PV_LIB_SPEC_DisjointCaptures18.n_typed, `PV_LIB_SPEC_DisjointCaptures18.f_typed, `PV_LIB_SPEC_DisjointCaptures18.tasks_typed, `PV_LIB_SPEC_DisjointCaptures18.closure, `PV_LIB_SPEC_DisjointCaptures18.entry_nonempty, `PV_LIB_SPEC_DisjointEntry18.slot, `PV_LIB_SPEC_DisjointEntry18.store, `PV_LIB_SPEC_DisjointEntry18.tlsState, `PV_LIB_SPEC_DisjointEntry18.hooksSlot, `PV_LIB_SPEC_DisjointEntry18.state, `PV_LIB_SPEC_DisjointEntry18.input, `PV_LIB_SPEC_DisjointEntry18.memory_before, `PV_LIB_SPEC_DisjointPre18.memory_before, `PV_LIB_SPEC_DisjointPre18.receivers, `PV_LIB_SPEC_DisjointPre18.run_bytes, `PV_LIB_SPEC_DisjointPre18.n_bytes, `PV_LIB_SPEC_DisjointPre18.run_typed, `PV_LIB_SPEC_DisjointPre18.n_typed, `PV_LIB_SPEC_DisjointPre18.f_typed, `PV_LIB_SPEC_DisjointPre18.tasks_typed, `PV_LIB_SPEC_DisjointPre18.fresh, `PV_LIB_SPEC_DisjointPre18.validity, `PV_LIB_SPEC_DisjointPre18.owner, `PV_LIB_SPEC_DisjointPre18.captured, `PV_LIB_SPEC_DisjointPre18.pre, `PV_LIB_SPEC_EntryWorld18.input, `PV_LIB_SPEC_EntryWorld18.StackGrant, `PV_LIB_SPEC_EntryWorld18.Entry, `PV_LIB_SPEC_EntryWorld18.frame, `PV_LIB_SPEC_EntryWorld18.paired, `PV_LIB_SPEC_EntryWorld18.stack_contains, `PV_LIB_SPEC_EntryWorld18.concrete_pre_data, `PV_LIB_SPEC_EntryWorld18.concrete, `PV_LIB_SPEC_EntryWorld18.concrete_pre, `PV_LIB_SPEC_EntryWorld18.inhabited, `PV_LIB_SPEC_Prefix54World18.original6, `PV_LIB_SPEC_Prefix54World18.original7, `PV_LIB_SPEC_Prefix54World18.original13, `PV_LIB_SPEC_Prefix54World18.original16, `PV_LIB_SPEC_Prefix54World18.original22, `PV_LIB_SPEC_Prefix54World18.original25, `PV_LIB_SPEC_Prefix54World18.original32, `PV_LIB_SPEC_Prefix54World18.original40, `PV_LIB_SPEC_Prefix54World18.original50, `PV_LIB_SPEC_Prefix54World18.original51, `PV_LIB_SPEC_Prefix54World18.original53, `PV_LIB_SPEC_Prefix54World18.original54, `PV_LIB_SPEC_World18_TlsAt54.at54, `PV_LIB_SPEC_World18_TlsNative15.physical, `PV_LIB_SPEC_World18_TlsNative15.active, `PV_LIB_SPEC_World18_TlsNative15.value, `PV_LIB_SPEC_World18_TlsBound15.answer, `PV_LIB_SPEC_World18_TlsDelivery15.after, `PV_LIB_SPEC_World18_TlsDelivery15.transition, `PV_LIB_SPEC_World18_TlsAt55.at55, `PV_LIB_SPEC_World18_TlsAt55.ordinary, `PV_LIB_SPEC_World18_TlsAt55.context, `PV_LIB_SPEC_World18_TlsAt55.consume, `PV_LIB_SPEC_World18_TlsAt55.original55, `PV_LIB_SPEC_World18_TlsAt58.at58, `PV_LIB_SPEC_World18_TlsAt58.original58, `PV_LIB_SPEC_World18_TlsAt58.first_native, `PV_LIB_SPEC_World18_TlsAt58.world58, `PV_LIB_SPEC_World18_Tls59Data15.after, `PV_LIB_SPEC_World18_Tls59Data15.at59, `PV_LIB_SPEC_World18_Tls59Data15.nonnative, `PV_LIB_SPEC_World18_Tls277Delivery15.transition, `PV_LIB_SPEC_World18_TlsAt59.context, `PV_LIB_SPEC_World18_TlsAt59.consume, `PV_LIB_SPEC_World18_TlsAt59.original59, `PV_LIB_SPEC_World18_TlsAt63.at63, `PV_LIB_SPEC_World18_TlsAt63.original63, `PV_LIB_SPEC_World18_TlsAt63.state63, `PV_LIB_SPEC_World18_TlsAt63.issued63, `PV_LIB_SPEC_World18_TlsAt63.consumed63, `PV_LIB_SPEC_World18_TlsAt63.world63, `PV_LIB_SPEC_World18_TlsAt63.entry, `PV_LIB_SPEC_World18_Tls64Data16.after, `PV_LIB_SPEC_World18_Tls64Data16.at64, `PV_LIB_SPEC_World18_Tls64Data16.nonnative, `PV_LIB_SPEC_World18_Tls278Delivery16.transition, `PV_LIB_SPEC_World18_TlsAt64.context, `PV_LIB_SPEC_World18_TlsAt64.consume, `PV_LIB_SPEC_World18_TlsAt64.original64, `PV_LIB_SPEC_World18_TlsAt67.at67, `PV_LIB_SPEC_World18_TlsAt67.original67, `PV_LIB_SPEC_World18_TlsAt67.state67, `PV_LIB_SPEC_World18_TlsAt67.issued67, `PV_LIB_SPEC_World18_TlsAt67.consumed67, `PV_LIB_SPEC_World18_TlsAt67.world67, `PV_LIB_SPEC_World18_TlsAt67.entry, `PV_LIB_SPEC_World18_Tls68Data16.after, `PV_LIB_SPEC_World18_Tls68Data16.at68, `PV_LIB_SPEC_World18_Tls68Data16.nonnative, `PV_LIB_SPEC_World18_Tls279Delivery16.transition, `PV_LIB_SPEC_World18_TlsAt68.context, `PV_LIB_SPEC_World18_TlsAt68.consume, `PV_LIB_SPEC_World18_TlsAt68.original68, `PV_LIB_SPEC_World18_TlsAt75.at75, `PV_LIB_SPEC_World18_TlsAt75.original75, `PV_LIB_SPEC_World18_TlsAt75.state75, `PV_LIB_SPEC_World18_TlsAt75.consumed75, `PV_LIB_SPEC_World18_TlsAt84.at84, `PV_LIB_SPEC_World18_TlsAt84.stage75, `PV_LIB_SPEC_World18_TlsAt84.dereference, `PV_LIB_SPEC_World18_TlsAt84.original84, `PV_LIB_SPEC_World18_TlsAt84.state84, `PV_LIB_SPEC_World18_TlsAt84.issued84, `PV_LIB_SPEC_World18_TlsAt84.consumed84, `PV_LIB_SPEC_World18_Tls18Reached16.active, `PV_LIB_SPEC_World18_Tls85Data16.after, `PV_LIB_SPEC_World18_Tls85Data16.at85, `PV_LIB_SPEC_World18_Tls85Data16.ordinary, `PV_LIB_SPEC_World18_Tls18Delivery16.transition, `PV_LIB_SPEC_World18_TlsAt85.context, `PV_LIB_SPEC_World18_TlsAt85.consume, `PV_LIB_SPEC_World18_TlsAt85.original85, `PV_LIB_SPEC_History18.history, `PV_LIB_SPEC_History18.original85, `PV_LIB_SPEC_History18.concrete85, `PV_LIB_SPEC_History18.world85, `PV_LIB_SPEC_History18.replies85, `PV_LIB_SPEC_History18.scheduled_heap_away])
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
