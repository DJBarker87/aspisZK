import Lean
import RPz7_T2Nat_NativePair
import RPz7_SdkD_FirstModel
import RPz7_SdkD_ReaderRoots
import RPz7_SdkD_WriterQueryCells
import RPz7_SdkD_WriterQueries
import RPz7_SdkD_ReaderQueries
import RPz7_SdkD_CheckpointBinding
import RPz7_SdkD_SecondModel
import RPz7_SdkC_GlobalRecovery
import RPz7_SdkC_Replay
import RPz7_SdkD_BatchUnion
import RPz7_SdkD_Tx1Suffix
import RPz7_SdkD_Tx1Run
import RPz7_SdkD_Install
import RPz7_SdkD_SecondCut
import RPz7_SdkD_PairBatches
import RPz7_SdkD_SecondRun
import RPz7_SdkD_ReplayPair
import RPz7_AuS1_Suffix
import RPz7_AuS1_Row30
import RPz7_AuS1_Absorb
import RPz7_AuS1_Block
import RPz7_AuS1_Frame
import RPz7_AuS1_Vec
import RPz7_AuS1_OriginalRead
import RPz7_AuS1_Sampling
import RPz7_AuS1_Prepared
import RPz7_AuS1_Semantic1
import RPz7_AuS1_Semantic2
import RPz7_AuS1_Semantic3
import RPz7_AuS1_Prepare
import RPz7_AuS1_Enclosing
import RPz7_AuS1_ClosedRead
import RPz7_AuS1_View
import RPz7_AuS1_ViewSource
import RPz7_AuS1_Offsets
import RPz7_AuS1_RootSource
import RPz7_AuS1_Observe
import RPz7_AuS1_PrepareRead
import RPz7_AuS1_Recovery
import RPz7_AuS1_Finish
import RPz7_AuS1_Pair
import RPz7_AuS1_Context
import RPz7_AuS1_OnRun
import RPz7_AuS1_Install
import RPz7_AuS1_Map
import RPz7_AuS1_Accepted
import RPz7_AuS1_Bound
import RPz7_EndP_Numeric
import RPz7_GExp_BudgetLaws
import RPz7_GExp_BudgetTactic
import RPz7_GExp_LeafBudget
import RPz7_GExp_NodeBudget
import RPz7_GExp_IdealValue
import RPz7_GExp_RowsBudget
import RPz7_GExp_CountLaws
import RPz7_GExp_LevelsBudget
import RPz7_GExp_CountTactic
import RPz7_GExp_VerifyBudget
import RPz7_GExp_BatchStepBudget
import RPz7_GExp_BatchLoopBudget
import RPz7_GExp_BatchTreeBudget
import RPz7_GExp_BatchBudget
import RPz7_GExp_FirstErasure
import RPz7_GExp_FirstSource
import RPz7_GExp_FirstAccepted
import RPz7_GExp_RetainedReader
import RPz7_GExp_SecondCode
import RPz7_GExp_SecondSource
import RPz7_GExp_CheckpointBudget
import RPz7_GExp_FirstBudget
import RPz7_GExp_SecondBudget
import RPz7_GExp_FirstPair
import RPz7_GExp_Accepted
import RPz7_GExp_SecondPair
import RPz7_GExp_PairAccepted
import RPz7_GExp_Experiment
import RPz7_GExp_GlobalBudget
import RPz7_GExp_CollisionBudget
import RPz7_EndP_Collision
import RPz7_EndP_AuthMass
import RPz7_EndP_Headline
import RPz7_DrvI_Counterexample
import RPz7_DrvI_Installation

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_T2Nat_NativePair, `RPz7_SdkD_FirstModel, `RPz7_SdkD_ReaderRoots, `RPz7_SdkD_WriterQueryCells, `RPz7_SdkD_WriterQueries, `RPz7_SdkD_ReaderQueries, `RPz7_SdkD_CheckpointBinding, `RPz7_SdkD_SecondModel, `RPz7_SdkC_GlobalRecovery, `RPz7_SdkC_Replay, `RPz7_SdkD_BatchUnion, `RPz7_SdkD_Tx1Suffix, `RPz7_SdkD_Tx1Run, `RPz7_SdkD_Install, `RPz7_SdkD_SecondCut, `RPz7_SdkD_PairBatches, `RPz7_SdkD_SecondRun, `RPz7_SdkD_ReplayPair, `RPz7_AuS1_Suffix, `RPz7_AuS1_Row30, `RPz7_AuS1_Absorb, `RPz7_AuS1_Block, `RPz7_AuS1_Frame, `RPz7_AuS1_Vec, `RPz7_AuS1_OriginalRead, `RPz7_AuS1_Sampling, `RPz7_AuS1_Prepared, `RPz7_AuS1_Semantic1, `RPz7_AuS1_Semantic2, `RPz7_AuS1_Semantic3, `RPz7_AuS1_Prepare, `RPz7_AuS1_Enclosing, `RPz7_AuS1_ClosedRead, `RPz7_AuS1_View, `RPz7_AuS1_ViewSource, `RPz7_AuS1_Offsets, `RPz7_AuS1_RootSource, `RPz7_AuS1_Observe, `RPz7_AuS1_PrepareRead, `RPz7_AuS1_Recovery, `RPz7_AuS1_Finish, `RPz7_AuS1_Pair, `RPz7_AuS1_Context, `RPz7_AuS1_OnRun, `RPz7_AuS1_Install, `RPz7_AuS1_Map, `RPz7_AuS1_Accepted, `RPz7_AuS1_Bound, `RPz7_EndP_Numeric, `RPz7_GExp_BudgetLaws, `RPz7_GExp_BudgetTactic, `RPz7_GExp_LeafBudget, `RPz7_GExp_NodeBudget, `RPz7_GExp_IdealValue, `RPz7_GExp_RowsBudget, `RPz7_GExp_CountLaws, `RPz7_GExp_LevelsBudget, `RPz7_GExp_CountTactic, `RPz7_GExp_VerifyBudget, `RPz7_GExp_BatchStepBudget, `RPz7_GExp_BatchLoopBudget, `RPz7_GExp_BatchTreeBudget, `RPz7_GExp_BatchBudget, `RPz7_GExp_FirstErasure, `RPz7_GExp_FirstSource, `RPz7_GExp_FirstAccepted, `RPz7_GExp_RetainedReader, `RPz7_GExp_SecondCode, `RPz7_GExp_SecondSource, `RPz7_GExp_CheckpointBudget, `RPz7_GExp_FirstBudget, `RPz7_GExp_SecondBudget, `RPz7_GExp_FirstPair, `RPz7_GExp_Accepted, `RPz7_GExp_SecondPair, `RPz7_GExp_PairAccepted, `RPz7_GExp_Experiment, `RPz7_GExp_GlobalBudget, `RPz7_GExp_CollisionBudget, `RPz7_EndP_Collision, `RPz7_EndP_AuthMass, `RPz7_EndP_Headline, `RPz7_DrvI_Counterexample, `RPz7_DrvI_Installation ]
  let phaseOwners : Array Name := #[ `RPz7_S1SemanticPrefixModelV1, `RPz7_S1SemanticFinishModelV1, `RPz7_S1SemanticFinishBoundsV1, `RPz7_ClaimsUnrolledFinish, `RPz7_S1SemanticVerifyReachabilityV1, `RPz7_S1SemanticFinishRootsV1, `RPz7_S1AcceptedSemanticNumericV1, `RPz7_S1AcceptedChallengesNumericV1, `RPz7_S1SemanticCodeFinishV1, `RPz7_S1SemanticCodeVerifyV1, `RPz7_S1SemanticCodeFinishExactV1, `RPz7_S1SemanticCodeVerifyExactV1, `RPz7_GExp_FinishAssociation, `RPz7_GExp_VerifyAssociation, `RPz7_S1SemanticBudgetV1, `RPz7_AuS1_Semantic3, `RPz7_F3V_SemanticFinish, `RPz7_F3V_SemanticVerify, `RPz7_RawJ_VerifyRead, `RPz7_RawK_VerifyHead, `RPz7_F3U_VerifyHead ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ7_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ7_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ7_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        if phaseOwners.contains owner || n.toString.startsWith "RPz7_PhaseIso" || n.toString == "AspisR1.Rc10_Top.deployed" then
          logInfo m!"RPZ7_KERNEL_TYPE {(Json.mkObj [("name", toJson n.toString), ("type", toJson (repr c.type).pretty)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ7_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ7_AUDIT_COMPLETE declarations={count} modules={selected.size}"
