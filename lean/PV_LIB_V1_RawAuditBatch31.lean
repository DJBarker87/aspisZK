import Lean
import PV_EVHB_OwnerRawWalker
open Lean Elab Command

-- V1_ARRAYS_BEGIN
@[noinline] private def v1Modules0 : Array Name := #[`PV_LIB_SPEC_TlsWorld18_1, `PV_LIB_SPEC_TlsWorld18_2, `PV_LIB_SPEC_TlsWorld18_3, `PV_LIB_SPEC_TlsWorld18_4, `PV_LIB_SPEC_TlsWorld18_5, `PV_LIB_SPEC_ToVec, `PV_LIB_SPEC_UnitReserve17, `PV_LIB_SPEC_UnitReserveTransport17, `PV_LIB_SPEC_V2Runtime, `PV_LIB_SPEC_Values14, `PV_LIB_SPEC_ValuesPrefix18, `PV_LIB_SPEC_VectorKinds14, `PV_LIB_SPEC_WordThreadArc, `PV_LIB_SPEC_WordThreadRecheck, `PV_LIB_SPEC_WordThreadRuntime, `PV_LIB_SPEC_Worker14]
@[noinline] private def v1Modules : Array Name := v1Modules0
@[noinline] private def v1Roots0 : Array Name := #[`PV_LIB_SPEC_ToVec.reference, `PV_LIB_SPEC_ToVec.start, `PV_LIB_SPEC_ToVec.statusView, `PV_LIB_SPEC_ToVec.storeView, `PV_LIB_SPEC_UnitReserve17.capacity, `PV_LIB_SPEC_UnitReserve17.old_rejects_unit, `PV_LIB_SPEC_UnitReserve17.other_functions, `PV_LIB_SPEC_UnitReserve17.reserve, `PV_LIB_SPEC_UnitReserve17.unit_no_growth, `PV_LIB_SPEC_UnitReserve17.values, `PV_LIB_SPEC_UnitReserveTransport17.append_graph, `PV_LIB_SPEC_UnitReserveTransport17.neutral, `PV_LIB_SPEC_V2Runtime.actions, `PV_LIB_SPEC_V2Runtime.control, `PV_LIB_SPEC_V2Runtime.preserves_owner_away, `PV_LIB_SPEC_V2Runtime.run, `PV_LIB_SPEC_V2Runtime.step, `PV_LIB_SPEC_V2Runtime.transition, `PV_LIB_SPEC_Values14.addNonNull, `PV_LIB_SPEC_Values14.growth_gap, `PV_LIB_SPEC_Values14.hooks_empty, `PV_LIB_SPEC_Values14.no_growth, `PV_LIB_SPEC_Values14.rawNonNull, `PV_LIB_SPEC_Values14.reserve, `PV_LIB_SPEC_Values14.subPointer, `PV_LIB_SPEC_Values14.values, `PV_LIB_SPEC_Values14.width, `PV_LIB_SPEC_ValuesPrefix18.NoWriter, `PV_LIB_SPEC_ValuesPrefix18.final_absent, `PV_LIB_SPEC_ValuesPrefix18.poll_absent, `PV_LIB_SPEC_ValuesPrefix18.prefix_absent, `PV_LIB_SPEC_VectorKinds14.innerKind, `PV_LIB_SPEC_VectorKinds14.markerKind, `PV_LIB_SPEC_VectorKinds14.rawKind, `PV_LIB_SPEC_VectorKinds14.vectorKind, `PV_LIB_SPEC_WordThreadArc.SiteType, `PV_LIB_SPEC_WordThreadArc.classify, `PV_LIB_SPEC_WordThreadArc.handler, `PV_LIB_SPEC_WordThreadArc.image, `PV_LIB_SPEC_WordThreadArc.layout_distinct, `PV_LIB_SPEC_WordThreadArc.packet_classified, `PV_LIB_SPEC_WordThreadArc.reply, `PV_LIB_SPEC_WordThreadArc.returned_owned, `PV_LIB_SPEC_WordThreadArc.scopeWord, `PV_LIB_SPEC_WordThreadArc.scope_classified, `PV_LIB_SPEC_WordThreadArc.scope_image_word, `PV_LIB_SPEC_WordThreadArc.shape, `PV_LIB_SPEC_WordThreadArc.threadWord, `PV_LIB_SPEC_WordThreadArc.thread_word, `PV_LIB_SPEC_WordThreadRecheck.packet_reply, `PV_LIB_SPEC_WordThreadRecheck.scope_handler, `PV_LIB_SPEC_WordThreadRecheck.thread_shape, `PV_LIB_SPEC_WordThreadRuntime.answer, `PV_LIB_SPEC_WordThreadRuntime.handler, `PV_LIB_SPEC_WordThreadRuntime.invalidPure, `PV_LIB_SPEC_WordThreadRuntime.native, `PV_LIB_SPEC_WordThreadRuntime.ordinary_framed, `PV_LIB_SPEC_WordThreadRuntime.valueAnswer, `PV_LIB_SPEC_Worker14.after, `PV_LIB_SPEC_Worker14.enter, `PV_LIB_SPEC_Worker14.issue, `PV_LIB_SPEC_Worker14.original, `PV_LIB_SPEC_Worker14.pending, `PV_LIB_SPEC_Worker14.push]
@[noinline] private def v1Roots1 : Array Name := #[`PV_LIB_SPEC_Worker14.site, `PV_LIB_SPEC_Worker14.store, `PV_LIB_SPEC_World18_Tls18Delivery16.transition, `PV_LIB_SPEC_World18_Tls18Reached16.active, `PV_LIB_SPEC_World18_Tls277Delivery15.transition, `PV_LIB_SPEC_World18_Tls278Delivery16.transition, `PV_LIB_SPEC_World18_Tls279Delivery16.transition, `PV_LIB_SPEC_World18_Tls59Data15.after, `PV_LIB_SPEC_World18_Tls59Data15.at59, `PV_LIB_SPEC_World18_Tls59Data15.nonnative, `PV_LIB_SPEC_World18_Tls64Data16.after, `PV_LIB_SPEC_World18_Tls64Data16.at64, `PV_LIB_SPEC_World18_Tls64Data16.nonnative, `PV_LIB_SPEC_World18_Tls68Data16.after, `PV_LIB_SPEC_World18_Tls68Data16.at68, `PV_LIB_SPEC_World18_Tls68Data16.nonnative, `PV_LIB_SPEC_World18_Tls85Data16.after, `PV_LIB_SPEC_World18_Tls85Data16.at85, `PV_LIB_SPEC_World18_Tls85Data16.ordinary, `PV_LIB_SPEC_World18_TlsAt54.at54, `PV_LIB_SPEC_World18_TlsAt55.at55, `PV_LIB_SPEC_World18_TlsAt55.consume, `PV_LIB_SPEC_World18_TlsAt55.context, `PV_LIB_SPEC_World18_TlsAt55.ordinary, `PV_LIB_SPEC_World18_TlsAt55.original55, `PV_LIB_SPEC_World18_TlsAt58.at58, `PV_LIB_SPEC_World18_TlsAt58.first_native, `PV_LIB_SPEC_World18_TlsAt58.original58, `PV_LIB_SPEC_World18_TlsAt58.world58, `PV_LIB_SPEC_World18_TlsAt59.consume, `PV_LIB_SPEC_World18_TlsAt59.context, `PV_LIB_SPEC_World18_TlsAt59.original59, `PV_LIB_SPEC_World18_TlsAt63.at63, `PV_LIB_SPEC_World18_TlsAt63.consumed63, `PV_LIB_SPEC_World18_TlsAt63.entry, `PV_LIB_SPEC_World18_TlsAt63.issued63, `PV_LIB_SPEC_World18_TlsAt63.original63, `PV_LIB_SPEC_World18_TlsAt63.state63, `PV_LIB_SPEC_World18_TlsAt63.world63, `PV_LIB_SPEC_World18_TlsAt64.consume, `PV_LIB_SPEC_World18_TlsAt64.context, `PV_LIB_SPEC_World18_TlsAt64.original64, `PV_LIB_SPEC_World18_TlsAt67.at67, `PV_LIB_SPEC_World18_TlsAt67.consumed67, `PV_LIB_SPEC_World18_TlsAt67.entry, `PV_LIB_SPEC_World18_TlsAt67.issued67, `PV_LIB_SPEC_World18_TlsAt67.original67, `PV_LIB_SPEC_World18_TlsAt67.state67, `PV_LIB_SPEC_World18_TlsAt67.world67, `PV_LIB_SPEC_World18_TlsAt68.consume, `PV_LIB_SPEC_World18_TlsAt68.context, `PV_LIB_SPEC_World18_TlsAt68.original68, `PV_LIB_SPEC_World18_TlsAt75.at75, `PV_LIB_SPEC_World18_TlsAt75.consumed75, `PV_LIB_SPEC_World18_TlsAt75.original75, `PV_LIB_SPEC_World18_TlsAt75.state75, `PV_LIB_SPEC_World18_TlsAt84.at84, `PV_LIB_SPEC_World18_TlsAt84.consumed84, `PV_LIB_SPEC_World18_TlsAt84.dereference, `PV_LIB_SPEC_World18_TlsAt84.issued84, `PV_LIB_SPEC_World18_TlsAt84.original84]
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
