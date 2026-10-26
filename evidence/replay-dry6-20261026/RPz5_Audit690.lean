import Lean
import RawSourceLiteralTraceLift
import RawSourceGlobalOracleCoupling
import RawSourceGlobalOracleInitial
import RawTx1DigestLog
import S1SemanticCodeSampleBlockV1
import S1SemanticCodeSampleBlockExactV1
import S1SemanticCodeSemanticValidatedV1
import S1SemanticCodeRoundStepV1
import S1SemanticCodeRoundsV1
import S1SemanticCodeCircleValidatedV1
import S1SemanticCodeFinishV1
import S1SemanticCodeBeginV1
import S1SemanticCodeNewTranscriptV1
import S1SemanticCodePublicTranscriptV1
import S1SemanticCodeVerifyV1
import S1SemanticCodeSemanticValidatedExactV1
import S1SemanticCodeRoundStepExactV1
import S1SemanticCodeRoundsExactV1
import S1SemanticCodeCircleValidatedExactV1
import S1SemanticCodeFinishExactV1
import S1SemanticCodeBeginExactV1
import S1SemanticCodeNewTranscriptExactV1
import S1SemanticCodePublicTranscriptExactV1
import S1SemanticCodeVerifyExactV1
import SdkD_PrepareLower
import PAln_OpeningCalls
import PAln_MatchingFacts
import F3L_MatchingChallenges
import F3L_RestoreChallenge
import F3L_GammaMeaning
import F3L_OrdinaryMeaning
import F3L_InputDiscovery
import F3L_LateFields
import F3L_TypedFields
import F3L_LateFieldEquality
import PSem_RoundCalls
import GExp_Association
import S1PrepareBudgetCoreV1
import S1PrepareBudgetTacticV1
import S1SemanticBudgetV1
import S1PreparedBudgetV1
import Port9OR_Batch
import F3L_WriterNumeric
import F3L_PreparedExt
import AspisR1CircleSampleWrapper.FunsExternal
import AspisR1CircleSampleWrapper.Funs
import AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw
import AspisR1CircleSampleWrapper.RawCircleSampleActualSamplerCanonicalV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualSecureBridgeV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackResultV4
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCircleV2
import AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyV2
import AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1
import R4TransportCircleCoordinates
import F3L_InputOpening
import F3M_ReaderChallenges
import F3M_OpeningReader
import F3N_ContextCoordinates
import ActualDecodeKStrictQM31Parser
import F3P_MatchingY
import ExtractedPrefixTypedFullCurrent
import ExtractedSourceFull25Typed
import RawSourceLiteralInitialCall
import PAln_SemanticRead
import F3M_MatchingInactive
import PAln_CircleCalls
import Port4B_CallerJoin
import Port4B_FoldedCut
import Port4C_Installed
import Port4A_Prefix
import Port4A_PrepareCut
import Port3_DecodeCoherence
import Port5Q2_Prepared
import Port5Q2_Advance
import Port5Q2_Ten
import Port5Q2_Provenance
import Port4A_CheckpointRows
import Port4A_PrefixReader
import Port5Q2_Checkpoint
import F3M_ChallengeTransport
import SAG_DotDecode
import SAG_QuarterBase
import SAG_UnrestrictedScale
import SAG_QuarterTransport
import SAG_QuarterLift
import SAG_Quarter
import SAG_StageScale
import Tx2N_Powers
import RowOrder_History
import T2Nat_Silent
import T2Nat_FinishCode
import T2Nat_FinishResult
import T2Nat_RawBounds
import T2Nat_RawJoin
import T2Nat_ResultEq
import T2Nat_CodeEq
import T2Nat_CodeIf
import T2Nat_ResumePrefix
import T2Nat_ResumeCode

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RawSourceLiteralTraceLift, `RawSourceGlobalOracleCoupling, `RawSourceGlobalOracleInitial, `RawTx1DigestLog, `S1SemanticCodeSampleBlockV1, `S1SemanticCodeSampleBlockExactV1, `S1SemanticCodeSemanticValidatedV1, `S1SemanticCodeRoundStepV1, `S1SemanticCodeRoundsV1, `S1SemanticCodeCircleValidatedV1, `S1SemanticCodeFinishV1, `S1SemanticCodeBeginV1, `S1SemanticCodeNewTranscriptV1, `S1SemanticCodePublicTranscriptV1, `S1SemanticCodeVerifyV1, `S1SemanticCodeSemanticValidatedExactV1, `S1SemanticCodeRoundStepExactV1, `S1SemanticCodeRoundsExactV1, `S1SemanticCodeCircleValidatedExactV1, `S1SemanticCodeFinishExactV1, `S1SemanticCodeBeginExactV1, `S1SemanticCodeNewTranscriptExactV1, `S1SemanticCodePublicTranscriptExactV1, `S1SemanticCodeVerifyExactV1, `SdkD_PrepareLower, `PAln_OpeningCalls, `PAln_MatchingFacts, `F3L_MatchingChallenges, `F3L_RestoreChallenge, `F3L_GammaMeaning, `F3L_OrdinaryMeaning, `F3L_InputDiscovery, `F3L_LateFields, `F3L_TypedFields, `F3L_LateFieldEquality, `PSem_RoundCalls, `GExp_Association, `S1PrepareBudgetCoreV1, `S1PrepareBudgetTacticV1, `S1SemanticBudgetV1, `S1PreparedBudgetV1, `Port9OR_Batch, `F3L_WriterNumeric, `F3L_PreparedExt, `AspisR1CircleSampleWrapper.FunsExternal, `AspisR1CircleSampleWrapper.Funs, `AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw, `AspisR1CircleSampleWrapper.RawCircleSampleActualSamplerCanonicalV1, `AspisR1CircleSampleWrapper.RawCircleSampleActualSecureBridgeV1, `AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackResultV4, `AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1, `AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCircleV2, `AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyV2, `AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1, `R4TransportCircleCoordinates, `F3L_InputOpening, `F3M_ReaderChallenges, `F3M_OpeningReader, `F3N_ContextCoordinates, `ActualDecodeKStrictQM31Parser, `F3P_MatchingY, `ExtractedPrefixTypedFullCurrent, `ExtractedSourceFull25Typed, `RawSourceLiteralInitialCall, `PAln_SemanticRead, `F3M_MatchingInactive, `PAln_CircleCalls, `Port4B_CallerJoin, `Port4B_FoldedCut, `Port4C_Installed, `Port4A_Prefix, `Port4A_PrepareCut, `Port3_DecodeCoherence, `Port5Q2_Prepared, `Port5Q2_Advance, `Port5Q2_Ten, `Port5Q2_Provenance, `Port4A_CheckpointRows, `Port4A_PrefixReader, `Port5Q2_Checkpoint, `F3M_ChallengeTransport, `SAG_DotDecode, `SAG_QuarterBase, `SAG_UnrestrictedScale, `SAG_QuarterTransport, `SAG_QuarterLift, `SAG_Quarter, `SAG_StageScale, `Tx2N_Powers, `RowOrder_History, `T2Nat_Silent, `T2Nat_FinishCode, `T2Nat_FinishResult, `T2Nat_RawBounds, `T2Nat_RawJoin, `T2Nat_ResultEq, `T2Nat_CodeEq, `T2Nat_CodeIf, `T2Nat_ResumePrefix, `T2Nat_ResumeCode ]
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
