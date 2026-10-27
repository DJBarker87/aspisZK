import Lean
import RPz7_DrvC_Carriers
import RPz7_DrvC_Program
import RPz7_DrvC_Installation
import RPz7_DrvC_Dictionary
import RPz7_DrvC_Implementation
import RPz7_DrvC_Headline
import RPz7_DrvC_CurrentSlots
import RPz7_DrvC_CallCode
import RPz7_DrvC_Effects
import RPz7_DrvC_Flow
import RPz7_DrvC_OraclePort
import RPz7_DrvC_FirstPure
import RPz7_DrvC_QueryTransport
import RPz7_DrvC_SecondFlow
import RPz7_DrvC_BatchDictionary
import RPz7_DrvC_MapCode
import RPz7_DrvC_FirstBatch
import RPz7_DrvC_FirstPrepare
import RPz7_DrvC_FirstPrograms
import RPz7_DrvC_FirstConstants
import RPz7_DrvC_OracleNormalize
import RPz7_DrvC_FirstLibrary
import RPz7_DrvC_FirstSyntax
import RPz7_DrvC_FirstHeadSyntax
import RPz7_DrvC_FirstHeadBridge
import RPz7_DrvC_Mutable
import RPz7_DrvC_FirstTail
import RPz7_DrvC_FirstHead
import RPz7_DrvC_FirstProgram
import RPz7_DrvC_SecondCode
import RPz7_DrvC_AuthenticatedCode
import RPz7_DrvC_SecondProgram
import RPz7_DrvC_PairProgram
import RPz7_DrvC_SourceEntry
import RPz7_DrvC_SourceHeadline
import RPz7_Cons_Ten
import RPz7_Cons_Finish
import RPz7_Cons_Native
import RPz7_Cons_Continuation
import RPz7_Cons_Base
import RPz7_Cons_Caller
import RPz7_Cons_Result
import RPz7_Cons_NativeBuild
import RPz7_Cons_FinishProof
import RPz7_Cons_Second
import RPz7_Cons_Pair
import RPz7_T2R_Parser
import RPz7_DrvC_Bytes
import RPz7_DrvC_NativeDecode
import RPz7_DrvC_AcceptedCalls
import RPz7_DrvC_DecodeCut
import RPz7_DrvC_CutAcceptance
import RPz7_DrvC_NativePair
import RPz7_DrvC_PublicCarrier
import RPz7_Par_Public
import RPz7_Par_NativePair
import RPz7_T2R_Nonvacuity
import RPz7_T2R_Acceptance
import RPz7_T2R_Ten
import RPz7_T2R_Reader
import RPz7_T2R_Finish
import RPz7_T2R_ContSource
import RPz7_T2R_CallerSource
import RPz7_Par_Headline
import RPz7_Par_Transcript
import RPz7_T2R_Public
import RPz7_T2R_PublicDecode
import RPz7_T2R_FullResult
import RPz7_T2R_ResultSource
import RPz7_T2R_Pair
import RPz7_T2R_Top
import RPz7_Rc2_Install
import RPz7_F3Q_CircleScope
import RPz7_SAP_Install
import RPz7_SAP_ConfigScope
import RPz7_Rc3_Install
import RPz7_SAQ_CompleteInstall
import RPz7_Rc4_Install
import RPz7_CPP_Install
import RPz7_CPH_Install
import RPz7_Rc5_Install
import RPz7_FIn_Install
import RPz7_FIn_WeightsInstall
import RPz7_FIo_Install

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_DrvC_Carriers, `RPz7_DrvC_Program, `RPz7_DrvC_Installation, `RPz7_DrvC_Dictionary, `RPz7_DrvC_Implementation, `RPz7_DrvC_Headline, `RPz7_DrvC_CurrentSlots, `RPz7_DrvC_CallCode, `RPz7_DrvC_Effects, `RPz7_DrvC_Flow, `RPz7_DrvC_OraclePort, `RPz7_DrvC_FirstPure, `RPz7_DrvC_QueryTransport, `RPz7_DrvC_SecondFlow, `RPz7_DrvC_BatchDictionary, `RPz7_DrvC_MapCode, `RPz7_DrvC_FirstBatch, `RPz7_DrvC_FirstPrepare, `RPz7_DrvC_FirstPrograms, `RPz7_DrvC_FirstConstants, `RPz7_DrvC_OracleNormalize, `RPz7_DrvC_FirstLibrary, `RPz7_DrvC_FirstSyntax, `RPz7_DrvC_FirstHeadSyntax, `RPz7_DrvC_FirstHeadBridge, `RPz7_DrvC_Mutable, `RPz7_DrvC_FirstTail, `RPz7_DrvC_FirstHead, `RPz7_DrvC_FirstProgram, `RPz7_DrvC_SecondCode, `RPz7_DrvC_AuthenticatedCode, `RPz7_DrvC_SecondProgram, `RPz7_DrvC_PairProgram, `RPz7_DrvC_SourceEntry, `RPz7_DrvC_SourceHeadline, `RPz7_Cons_Ten, `RPz7_Cons_Finish, `RPz7_Cons_Native, `RPz7_Cons_Continuation, `RPz7_Cons_Base, `RPz7_Cons_Caller, `RPz7_Cons_Result, `RPz7_Cons_NativeBuild, `RPz7_Cons_FinishProof, `RPz7_Cons_Second, `RPz7_Cons_Pair, `RPz7_T2R_Parser, `RPz7_DrvC_Bytes, `RPz7_DrvC_NativeDecode, `RPz7_DrvC_AcceptedCalls, `RPz7_DrvC_DecodeCut, `RPz7_DrvC_CutAcceptance, `RPz7_DrvC_NativePair, `RPz7_DrvC_PublicCarrier, `RPz7_Par_Public, `RPz7_Par_NativePair, `RPz7_T2R_Nonvacuity, `RPz7_T2R_Acceptance, `RPz7_T2R_Ten, `RPz7_T2R_Reader, `RPz7_T2R_Finish, `RPz7_T2R_ContSource, `RPz7_T2R_CallerSource, `RPz7_Par_Headline, `RPz7_Par_Transcript, `RPz7_T2R_Public, `RPz7_T2R_PublicDecode, `RPz7_T2R_FullResult, `RPz7_T2R_ResultSource, `RPz7_T2R_Pair, `RPz7_T2R_Top, `RPz7_Rc2_Install, `RPz7_F3Q_CircleScope, `RPz7_SAP_Install, `RPz7_SAP_ConfigScope, `RPz7_Rc3_Install, `RPz7_SAQ_CompleteInstall, `RPz7_Rc4_Install, `RPz7_CPP_Install, `RPz7_CPH_Install, `RPz7_Rc5_Install, `RPz7_FIn_Install, `RPz7_FIn_WeightsInstall, `RPz7_FIo_Install ]
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
