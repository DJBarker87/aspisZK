import Lean
import RPz7_FIs_Finish
import RPz7_SAG_CommonFull
import RPz7_SAG_ViewTail
import RPz7_SAG_NativeFull
import RPz7_FIs_Native
import RPz7_SAG_ViewBytes
import RPz7_SAG_PhysicalShape
import RPz7_FIn_PhysicalRounds
import RPz7_SAG_FinalPayload
import RPz7_FIn_Payloads
import RPz7_FIn_Round
import RPz7_FIn_FromRead
import RPz7_FIn_WeightLength
import RPz7_SAG_DotFromPayload
import RPz7_SAG_DotFromRead
import RPz7_SAG_ShapeDot
import RPz7_FIs_OnRun
import RPz7_FIs_Literal
import RPz7_FIs_Cont
import RPz7_FIs_Caller
import RPz7_P2P_Acceptance
import RPz7_CPP_Acceptance
import RPz7_TxS_Writer
import RPz7_TxS_RawTen
import RPz7_TxS_Encoding
import RPz7_Rc4_Encoding
import RPz7_SAP_FinishSaved
import RPz7_SAP_LiteralOutcome
import RPz7_SAP_LiteralCont
import RPz7_SAP_LiteralCaller
import RPz7_SAP_Nonvacuity
import RPz7_Rc3_Nonvacuity
import RPz7_NP6_ClaimsModel
import RPz7_NP6_ClaimsSuccess
import RPz7_NP6_ClaimsMain
import RPz7_NP6_ClaimsRun
import RPz7_NP6_RecordShape
import RPz7_NP6_ParsedClaims
import RPz7_RowShape_SlotObstruction
import RPz7_Op4P_Audit
import RPz7_Tx1Q_Nonvacuity
import RPz7_NP6_Constructors
import RPz7_Rc2_Base
import RPz7_Rc3_Result
import RPz7_TxS_RawPublic
import RPz7_Rc5_Nonvacuity
import RPz7_FIs_P2P_R5Result
import RPz7_Rc5_Result
import RPz7_Rc6_Caller
import RPz7_PFin_Packet
import RPz7_P6C_Extension
import RPz7_P6C_Pair
import RPz7_SdkD_BatchLoopFixed
import RPz7_SdkD_BatchFixed
import RPz7_P6C_Batches
import RPz7_P6C_OnCuts
import RPz7_P6C_Whole
import RPz7_P6C_Callbacks
import RPz7_P6C_Issued
import RPz7_P6C_FullBoundary
import RPz7_FIs_P2P_Result
import RPz7_P2P_R5Result
import RPz7_FIs_Result
import RPz7_SAF_C_T2R_CallerSource
import RPz7_FIs_P2P_R3Result
import RPz7_SAF_C_Rc3_Result
import RPz7_FIs_P2P_SafResult
import RPz7_SAF_C_SAF_Result
import RPz7_FIs_P2P_FinalResult
import RPz7_SAF_C_SAF_FinalResult
import RPz7_Rc2_Result
import RPz7_Hir_PartialPrefix
import RPz7_GExq_BatchSource
import RPz7_GExq_FirstCode
import RPz7_GExq_FirstErasure
import RPz7_GExq_FirstSource
import RPz7_GExq_RetainedReader
import RPz7_GExq_SecondCode
import RPz7_GExq_SecondSource
import RPz7_GExq_ChildCode
import RPz7_GExq_OuterLower
import RPz7_GExq_OuterGoodLaws
import RPz7_GExq_OuterGoodFirst
import RPz7_GExq_GoodTactic

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_FIs_Finish, `RPz7_SAG_CommonFull, `RPz7_SAG_ViewTail, `RPz7_SAG_NativeFull, `RPz7_FIs_Native, `RPz7_SAG_ViewBytes, `RPz7_SAG_PhysicalShape, `RPz7_FIn_PhysicalRounds, `RPz7_SAG_FinalPayload, `RPz7_FIn_Payloads, `RPz7_FIn_Round, `RPz7_FIn_FromRead, `RPz7_FIn_WeightLength, `RPz7_SAG_DotFromPayload, `RPz7_SAG_DotFromRead, `RPz7_SAG_ShapeDot, `RPz7_FIs_OnRun, `RPz7_FIs_Literal, `RPz7_FIs_Cont, `RPz7_FIs_Caller, `RPz7_P2P_Acceptance, `RPz7_CPP_Acceptance, `RPz7_TxS_Writer, `RPz7_TxS_RawTen, `RPz7_TxS_Encoding, `RPz7_Rc4_Encoding, `RPz7_SAP_FinishSaved, `RPz7_SAP_LiteralOutcome, `RPz7_SAP_LiteralCont, `RPz7_SAP_LiteralCaller, `RPz7_SAP_Nonvacuity, `RPz7_Rc3_Nonvacuity, `RPz7_NP6_ClaimsModel, `RPz7_NP6_ClaimsSuccess, `RPz7_NP6_ClaimsMain, `RPz7_NP6_ClaimsRun, `RPz7_NP6_RecordShape, `RPz7_NP6_ParsedClaims, `RPz7_RowShape_SlotObstruction, `RPz7_Op4P_Audit, `RPz7_Tx1Q_Nonvacuity, `RPz7_NP6_Constructors, `RPz7_Rc2_Base, `RPz7_Rc3_Result, `RPz7_TxS_RawPublic, `RPz7_Rc5_Nonvacuity, `RPz7_FIs_P2P_R5Result, `RPz7_Rc5_Result, `RPz7_Rc6_Caller, `RPz7_PFin_Packet, `RPz7_P6C_Extension, `RPz7_P6C_Pair, `RPz7_SdkD_BatchLoopFixed, `RPz7_SdkD_BatchFixed, `RPz7_P6C_Batches, `RPz7_P6C_OnCuts, `RPz7_P6C_Whole, `RPz7_P6C_Callbacks, `RPz7_P6C_Issued, `RPz7_P6C_FullBoundary, `RPz7_FIs_P2P_Result, `RPz7_P2P_R5Result, `RPz7_FIs_Result, `RPz7_SAF_C_T2R_CallerSource, `RPz7_FIs_P2P_R3Result, `RPz7_SAF_C_Rc3_Result, `RPz7_FIs_P2P_SafResult, `RPz7_SAF_C_SAF_Result, `RPz7_FIs_P2P_FinalResult, `RPz7_SAF_C_SAF_FinalResult, `RPz7_Rc2_Result, `RPz7_Hir_PartialPrefix, `RPz7_GExq_BatchSource, `RPz7_GExq_FirstCode, `RPz7_GExq_FirstErasure, `RPz7_GExq_FirstSource, `RPz7_GExq_RetainedReader, `RPz7_GExq_SecondCode, `RPz7_GExq_SecondSource, `RPz7_GExq_ChildCode, `RPz7_GExq_OuterLower, `RPz7_GExq_OuterGoodLaws, `RPz7_GExq_OuterGoodFirst, `RPz7_GExq_GoodTactic ]
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
