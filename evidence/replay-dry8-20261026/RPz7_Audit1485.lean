import Lean
import RPz7_SInt2_S1SdkPreparedChallengeRangesV1
import RPz7_SInt2_S6SdkSelectedSemanticCutV1
import RPz7_SInt2_S6SdkSelectedSemanticCallerV1
import RPz7_SInt2_S1SdkSelectedSemanticTraceV1
import RPz7_ClaimsUnrolledFinishAdapters
import RPz7_ClaimsUnrolledVerify
import RPz7_SInt2_ClaimsUnrolledSdk
import RPz7_SInt2_AcceptedPairClaims
import RPz7_RowShape_InstalledSlots
import RPz7_Tx1Q_Carriers
import RPz7_Tx1Q_Install
import RPz7_Tx1Q_QueryBridge
import RPz7_Tx1Q_PrefixInstall
import RPz7_Op3I_Install
import RPz7_Op4P_Install
import RPz7_Op3I_Cuts
import RPz7_Op4P_Cuts
import RPz7_Tx1Q_Cuts
import RPz7_Tx1Q_Execution
import RPz7_PSem_SourceCuts
import RPz7_PSem_TypedPrefix
import RPz7_PSem_RecordChain
import RPz7_PSem_Slices
import RPz7_PSem_Lenses
import RPz7_PSem_Control
import RPz7_PSem_RowStep
import RPz7_PSem_RowControl
import RPz7_PSem_Iterator
import RPz7_PSem_Loop
import RPz7_PSem_Expansion
import RPz7_PSem_Lengths
import RPz7_PSem_SourceRows
import RPz7_PSem_Validation
import RPz7_PSem_Strict
import RPz7_PSem_SemanticRows
import RPz7_PAln_RowBounds
import RPz7_PAln_Arithmetic
import RPz7_PAln_Offsets
import RPz7_PAln_ViewCuts
import RPz7_PAln_Physical
import RPz7_F3J_InputRows
import RPz7_F3J_SamplerRun
import RPz7_F3J_QueryLog
import RPz7_RawSourceDigestLog
import RPz7_ExtractedSourceSemanticSampler
import RPz7_RawSourceLiteralSamplerStep
import RPz7_RawSourceLiteralTraceLift
import RPz7_RawSourceGlobalOracleCoupling
import RPz7_RawSourceGlobalOracleInitial
import RPz7_RawTx1DigestLog
import RPz7_F3J_SemanticLog
import RPz7_F3J_QueryPairs
import RPz7_F3J_QueryRow
import RPz7_S1SemanticCodeSampleBlockV1
import RPz7_S1SemanticCodeSampleBlockExactV1
import RPz7_F3J_BlockCalls
import RPz7_S1SemanticCodeSemanticValidatedV1
import RPz7_S1SemanticCodeRoundStepV1
import RPz7_S1SemanticCodeRoundsV1
import RPz7_S1SemanticCodeCircleValidatedV1
import RPz7_S1SemanticCodeFinishV1
import RPz7_S1SemanticCodeBeginV1
import RPz7_S1SemanticCodeNewTranscriptV1
import RPz7_S1SemanticCodePublicTranscriptV1
import RPz7_S1SemanticCodeVerifyV1
import RPz7_S1SemanticCodeSemanticValidatedExactV1
import RPz7_S1SemanticCodeRoundStepExactV1
import RPz7_S1SemanticCodeRoundsExactV1
import RPz7_S1SemanticCodeCircleValidatedExactV1
import RPz7_S1SemanticCodeFinishExactV1
import RPz7_S1SemanticCodeBeginExactV1
import RPz7_S1SemanticCodeNewTranscriptExactV1
import RPz7_S1SemanticCodePublicTranscriptExactV1
import RPz7_S1SemanticCodeVerifyExactV1
import RPz7_S1SemanticCurrentCodeV1
import RPz7_S1CurrentPrepareCodeV1
import RPz7_S1CurrentPrepareCodeExactV1
import RPz7_SdkD_PrepareLower
import RPz7_SdkD_PrepareSource
import RPz7_AuS1_Association
import RPz7_AuS1_Hash
import RPz7_F3J_ReseedSource
import RPz7_PAln_OpeningCalls
import RPz7_F3J_OpeningFacts

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_SInt2_S1SdkPreparedChallengeRangesV1, `RPz7_SInt2_S6SdkSelectedSemanticCutV1, `RPz7_SInt2_S6SdkSelectedSemanticCallerV1, `RPz7_SInt2_S1SdkSelectedSemanticTraceV1, `RPz7_ClaimsUnrolledFinishAdapters, `RPz7_ClaimsUnrolledVerify, `RPz7_SInt2_ClaimsUnrolledSdk, `RPz7_SInt2_AcceptedPairClaims, `RPz7_RowShape_InstalledSlots, `RPz7_Tx1Q_Carriers, `RPz7_Tx1Q_Install, `RPz7_Tx1Q_QueryBridge, `RPz7_Tx1Q_PrefixInstall, `RPz7_Op3I_Install, `RPz7_Op4P_Install, `RPz7_Op3I_Cuts, `RPz7_Op4P_Cuts, `RPz7_Tx1Q_Cuts, `RPz7_Tx1Q_Execution, `RPz7_PSem_SourceCuts, `RPz7_PSem_TypedPrefix, `RPz7_PSem_RecordChain, `RPz7_PSem_Slices, `RPz7_PSem_Lenses, `RPz7_PSem_Control, `RPz7_PSem_RowStep, `RPz7_PSem_RowControl, `RPz7_PSem_Iterator, `RPz7_PSem_Loop, `RPz7_PSem_Expansion, `RPz7_PSem_Lengths, `RPz7_PSem_SourceRows, `RPz7_PSem_Validation, `RPz7_PSem_Strict, `RPz7_PSem_SemanticRows, `RPz7_PAln_RowBounds, `RPz7_PAln_Arithmetic, `RPz7_PAln_Offsets, `RPz7_PAln_ViewCuts, `RPz7_PAln_Physical, `RPz7_F3J_InputRows, `RPz7_F3J_SamplerRun, `RPz7_F3J_QueryLog, `RPz7_RawSourceDigestLog, `RPz7_ExtractedSourceSemanticSampler, `RPz7_RawSourceLiteralSamplerStep, `RPz7_RawSourceLiteralTraceLift, `RPz7_RawSourceGlobalOracleCoupling, `RPz7_RawSourceGlobalOracleInitial, `RPz7_RawTx1DigestLog, `RPz7_F3J_SemanticLog, `RPz7_F3J_QueryPairs, `RPz7_F3J_QueryRow, `RPz7_S1SemanticCodeSampleBlockV1, `RPz7_S1SemanticCodeSampleBlockExactV1, `RPz7_F3J_BlockCalls, `RPz7_S1SemanticCodeSemanticValidatedV1, `RPz7_S1SemanticCodeRoundStepV1, `RPz7_S1SemanticCodeRoundsV1, `RPz7_S1SemanticCodeCircleValidatedV1, `RPz7_S1SemanticCodeFinishV1, `RPz7_S1SemanticCodeBeginV1, `RPz7_S1SemanticCodeNewTranscriptV1, `RPz7_S1SemanticCodePublicTranscriptV1, `RPz7_S1SemanticCodeVerifyV1, `RPz7_S1SemanticCodeSemanticValidatedExactV1, `RPz7_S1SemanticCodeRoundStepExactV1, `RPz7_S1SemanticCodeRoundsExactV1, `RPz7_S1SemanticCodeCircleValidatedExactV1, `RPz7_S1SemanticCodeFinishExactV1, `RPz7_S1SemanticCodeBeginExactV1, `RPz7_S1SemanticCodeNewTranscriptExactV1, `RPz7_S1SemanticCodePublicTranscriptExactV1, `RPz7_S1SemanticCodeVerifyExactV1, `RPz7_S1SemanticCurrentCodeV1, `RPz7_S1CurrentPrepareCodeV1, `RPz7_S1CurrentPrepareCodeExactV1, `RPz7_SdkD_PrepareLower, `RPz7_SdkD_PrepareSource, `RPz7_AuS1_Association, `RPz7_AuS1_Hash, `RPz7_F3J_ReseedSource, `RPz7_PAln_OpeningCalls, `RPz7_F3J_OpeningFacts ]
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
