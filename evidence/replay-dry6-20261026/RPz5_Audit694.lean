import Lean
import F3V_PreparedGeneric
import F3V_CheckpointCongr
import F3S_BatchLoop
import F3S_BatchTree
import F3R_FinishTailCode
import F3R_FinishSource
import F3S_RoundValues
import F3S_FinishReached
import F3S_RoundUnique
import F3S_FinishWitness
import F3S_FinishUnique
import RowOrder_FrozenSchedule
import RawK_ModelHead
import F3Q_CodeEval
import F3Q_IdealCode
import F3Q_BatchValue
import F3Q_TreeCode
import F3Q_LeafPost
import F3Q_LeafEval
import F3Q_LeafActive
import F3Q_SelectedLeaf
import F3Q_CodeLog
import F3Q_LeafLoop
import F3Q_TailView
import F3Q_TailTransport
import F3Q_TerminalLog
import F3Q_VerifyGuards
import F3N_PhysicalCode
import F3N_PhysicalNode
import F3N_PhysicalBind
import F3N_PhysicalRows
import F3N_PhysicalLevels
import F3N_P6LevelLog
import F3Q_VerifyLog
import F3Q_VerifyAccepted
import F3Q_VerifyCall
import F3Q_TailFacts
import F3Q_TailLog
import F3Q_TreeLog
import F3Q_TreeValue
import F3Q_BatchCodeLog
import F3Q_BatchLog
import F3N_ProgramCarrier
import Port8EFF_Bodies
import Port8EFF_Budget
import Port9OR_Bodies
import Port9OR_Installed
import F3Q_SliceIdentity
import F3N_FinishLog
import F3N_SourceEffect
import F3S_EffectDictionary
import F3S_EffectLog
import F3S_ReaderSkeleton
import F3U_RehashValue

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `F3V_PreparedGeneric, `F3V_CheckpointCongr, `F3S_BatchLoop, `F3S_BatchTree, `F3R_FinishTailCode, `F3R_FinishSource, `F3S_RoundValues, `F3S_FinishReached, `F3S_RoundUnique, `F3S_FinishWitness, `F3S_FinishUnique, `RowOrder_FrozenSchedule, `RawK_ModelHead, `F3Q_CodeEval, `F3Q_IdealCode, `F3Q_BatchValue, `F3Q_TreeCode, `F3Q_LeafPost, `F3Q_LeafEval, `F3Q_LeafActive, `F3Q_SelectedLeaf, `F3Q_CodeLog, `F3Q_LeafLoop, `F3Q_TailView, `F3Q_TailTransport, `F3Q_TerminalLog, `F3Q_VerifyGuards, `F3N_PhysicalCode, `F3N_PhysicalNode, `F3N_PhysicalBind, `F3N_PhysicalRows, `F3N_PhysicalLevels, `F3N_P6LevelLog, `F3Q_VerifyLog, `F3Q_VerifyAccepted, `F3Q_VerifyCall, `F3Q_TailFacts, `F3Q_TailLog, `F3Q_TreeLog, `F3Q_TreeValue, `F3Q_BatchCodeLog, `F3Q_BatchLog, `F3N_ProgramCarrier, `Port8EFF_Bodies, `Port8EFF_Budget, `Port9OR_Bodies, `Port9OR_Installed, `F3Q_SliceIdentity, `F3N_FinishLog, `F3N_SourceEffect, `F3S_EffectDictionary, `F3S_EffectLog, `F3S_ReaderSkeleton, `F3U_RehashValue ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ5_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ5_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ5_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ5_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ5_AUDIT_COMPLETE declarations={count} modules={selected.size}"
