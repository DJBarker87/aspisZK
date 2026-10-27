import Lean
import RPz7_SAF_C_SAP_SourceOutcome
import RPz7_SAF_C_SAP_ActualCont
import RPz7_SAF_C_SAP_ActualCaller
import RPz7_FIs_P2P_ActualResult
import RPz7_SAF_C_SAP_PairSelected
import RPz7_SAF_C_SAP_ActualResult
import RPz7_SAF_C_SAP_SourceConsumer
import RPz7_FIs_P2P_ActualPair
import RPz7_SAF_C_SAP_ClosedOutcome
import RPz7_SAF_C_SAP_ClosedCont
import RPz7_SAF_C_SAP_ClosedCaller
import RPz7_FIs_P2P_ClosedResult
import RPz7_SAF_C_SAP_ActualPair
import RPz7_SAF_C_SAP_CloseConsumer
import RPz7_SAF_C_SAP_ClosedResult
import RPz7_FIs_P2P_ClosedPair
import RPz7_SAF_C_SAP_DirectOutcome
import RPz7_SAF_C_SAP_DirectCont
import RPz7_SAF_C_SAP_DirectCaller
import RPz7_FIs_P2P_DirectResult
import RPz7_SAF_C_SAP_ClosedPair
import RPz7_SAF_C_SAP_DirectConsumer
import RPz7_SAF_C_SAP_DirectResult
import RPz7_FIs_P2P_DirectPair
import RPz7_FIs_P2P_LiteralResult
import RPz7_SAF_C_SAP_DirectPair
import RPz7_SAF_C_SAP_LiteralConsumer
import RPz7_SAF_C_SAP_LiteralResult
import RPz7_FIs_P2P_LiteralPair
import RPz7_FIs_P2P_LiteralFull
import RPz7_SAF_C_SAP_LiteralFull
import RPz7_SAF_C_SAP_LiteralPair
import RPz7_SAP_Binding
import RPz7_FIs_P2P_LiteralTop
import RPz7_SAF_C_SAP_LiteralTop
import RPz7_CPS_SourceTop
import RPz7_Rc2_Events
import RPz7_Rc2_Protection
import RPz7_FIs_P2P_R3Top
import RPz7_SAF_C_Rc3_Top
import RPz7_FIs_P2P_SafTop
import RPz7_SAF_C_SAF_Top
import RPz7_FIs_P2P_FinalTop
import RPz7_SAF_C_SAF_FinalTop
import RPz7_SAP_LiteralFull
import RPz7_SAP_ResultSelected
import RPz7_SAP_PairSelected
import RPz7_SAP_SourceOutcome
import RPz7_SAP_ActualCont
import RPz7_SAP_ActualCaller
import RPz7_SAP_ActualResult
import RPz7_SAP_SourceConsumer
import RPz7_SAP_ActualPair
import RPz7_SAP_ClosedOutcome
import RPz7_SAP_CloseConsumer
import RPz7_SAP_ClosedCont
import RPz7_SAP_ClosedCaller
import RPz7_SAP_ClosedResult
import RPz7_SAP_ClosedPair
import RPz7_SAP_DirectOutcome
import RPz7_SAP_DirectConsumer
import RPz7_SAP_DirectCont
import RPz7_SAP_DirectCaller
import RPz7_SAP_DirectResult
import RPz7_SAP_DirectPair
import RPz7_SAP_LiteralConsumer
import RPz7_SAP_LiteralResult
import RPz7_SAP_LiteralPair
import RPz7_SAP_LiteralTop
import RPz7_SAF_FinishSaved
import RPz7_SAF_FinishPrepared
import RPz7_SAF_LiteralOutcome
import RPz7_SAF_PreparedOutcome
import RPz7_SAF_LiteralCont
import RPz7_SAF_PreparedCont
import RPz7_SAF_LiteralCaller
import RPz7_SAF_PreparedCaller
import RPz7_SAF_Result
import RPz7_SAF_FinalResult
import RPz7_Rc3_Top
import RPz7_SAF_Top
import RPz7_FIs_P2P_Deployed
import RPz7_FIs_P2P_Extract
import RPz7_SAF_Deployed

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_SAF_C_SAP_SourceOutcome, `RPz7_SAF_C_SAP_ActualCont, `RPz7_SAF_C_SAP_ActualCaller, `RPz7_FIs_P2P_ActualResult, `RPz7_SAF_C_SAP_PairSelected, `RPz7_SAF_C_SAP_ActualResult, `RPz7_SAF_C_SAP_SourceConsumer, `RPz7_FIs_P2P_ActualPair, `RPz7_SAF_C_SAP_ClosedOutcome, `RPz7_SAF_C_SAP_ClosedCont, `RPz7_SAF_C_SAP_ClosedCaller, `RPz7_FIs_P2P_ClosedResult, `RPz7_SAF_C_SAP_ActualPair, `RPz7_SAF_C_SAP_CloseConsumer, `RPz7_SAF_C_SAP_ClosedResult, `RPz7_FIs_P2P_ClosedPair, `RPz7_SAF_C_SAP_DirectOutcome, `RPz7_SAF_C_SAP_DirectCont, `RPz7_SAF_C_SAP_DirectCaller, `RPz7_FIs_P2P_DirectResult, `RPz7_SAF_C_SAP_ClosedPair, `RPz7_SAF_C_SAP_DirectConsumer, `RPz7_SAF_C_SAP_DirectResult, `RPz7_FIs_P2P_DirectPair, `RPz7_FIs_P2P_LiteralResult, `RPz7_SAF_C_SAP_DirectPair, `RPz7_SAF_C_SAP_LiteralConsumer, `RPz7_SAF_C_SAP_LiteralResult, `RPz7_FIs_P2P_LiteralPair, `RPz7_FIs_P2P_LiteralFull, `RPz7_SAF_C_SAP_LiteralFull, `RPz7_SAF_C_SAP_LiteralPair, `RPz7_SAP_Binding, `RPz7_FIs_P2P_LiteralTop, `RPz7_SAF_C_SAP_LiteralTop, `RPz7_CPS_SourceTop, `RPz7_Rc2_Events, `RPz7_Rc2_Protection, `RPz7_FIs_P2P_R3Top, `RPz7_SAF_C_Rc3_Top, `RPz7_FIs_P2P_SafTop, `RPz7_SAF_C_SAF_Top, `RPz7_FIs_P2P_FinalTop, `RPz7_SAF_C_SAF_FinalTop, `RPz7_SAP_LiteralFull, `RPz7_SAP_ResultSelected, `RPz7_SAP_PairSelected, `RPz7_SAP_SourceOutcome, `RPz7_SAP_ActualCont, `RPz7_SAP_ActualCaller, `RPz7_SAP_ActualResult, `RPz7_SAP_SourceConsumer, `RPz7_SAP_ActualPair, `RPz7_SAP_ClosedOutcome, `RPz7_SAP_CloseConsumer, `RPz7_SAP_ClosedCont, `RPz7_SAP_ClosedCaller, `RPz7_SAP_ClosedResult, `RPz7_SAP_ClosedPair, `RPz7_SAP_DirectOutcome, `RPz7_SAP_DirectConsumer, `RPz7_SAP_DirectCont, `RPz7_SAP_DirectCaller, `RPz7_SAP_DirectResult, `RPz7_SAP_DirectPair, `RPz7_SAP_LiteralConsumer, `RPz7_SAP_LiteralResult, `RPz7_SAP_LiteralPair, `RPz7_SAP_LiteralTop, `RPz7_SAF_FinishSaved, `RPz7_SAF_FinishPrepared, `RPz7_SAF_LiteralOutcome, `RPz7_SAF_PreparedOutcome, `RPz7_SAF_LiteralCont, `RPz7_SAF_PreparedCont, `RPz7_SAF_LiteralCaller, `RPz7_SAF_PreparedCaller, `RPz7_SAF_Result, `RPz7_SAF_FinalResult, `RPz7_Rc3_Top, `RPz7_SAF_Top, `RPz7_FIs_P2P_Deployed, `RPz7_FIs_P2P_Extract, `RPz7_SAF_Deployed ]
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
