import Lean
import RPz7_FIp_DotDecode
import RPz7_FIp_NativeDots
import RPz7_FIp_DotsAdapter
import RPz7_FIp_Equality
import RPz7_FIp_SemanticArithmetic
import RPz7_FIp_Install
import RPz7_PAln_JoinedRun
import RPz7_F3L_PreparedPort
import RPz7_PFin_Gates
import RPz7_PFin_Prepared
import RPz7_PFin_Digest
import RPz7_PAln_Oracle
import RPz7_PFin_Attach
import RPz7_SAF_C_Cons_Finish
import RPz7_SAF_C_T2R_Finish
import RPz7_SAF_C_T2R_ContSource
import RPz7_SAP_CurrentNumeric
import RPz7_SAP_NumericFields
import RPz7_SAP_NumericTransport
import RPz7_SAP_LiteralFields
import RPz7_SAF_SavedIdentities
import RPz7_SAF_PreparedPairing
import RPz7_SAF_ReducedLaws
import RPz7_SAF_C_SAP_FinishConsumer
import RPz7_SAF_C_SAP_FinishSaved
import RPz7_SAF_C_SAF_FinishSaved
import RPz7_SAF_C_SAF_FinishPrepared
import RPz7_F3N_WriterReturned
import RPz7_F3L_WriterAlpha
import RPz7_F3L_WriterSemanticAlpha
import RPz7_F3L_WriterCoordinates
import RPz7_F3L_WriterRemaining
import RPz7_F3L_WriterPreparedEq
import RPz7_F3L_WriterBody
import RPz7_F3N_WriterNumeric
import RPz7_F3N_WriterOnRun
import RPz7_F3N_ConsDictionary
import RPz7_F3N_SameOracle
import RPz7_SAP_Cuts
import RPz7_SAP_CanonicalCarrier
import RPz7_SAP_OpeningCuts
import RPz7_SAP_OpeningShape
import RPz7_SAP_SampleCanonical
import RPz7_SAP_SemanticCanonical
import RPz7_SAP_WrapperCanonical
import RPz7_SAP_CircleCanonical
import RPz7_SAP_SemanticCircles
import RPz7_SAP_AlphaTransport
import RPz7_SAP_CoordinateTransport
import RPz7_SAP_PreparedFields
import RPz7_SAP_PrepareOwner
import RPz7_SAP_SaveOnRun
import RPz7_F3P_SemanticY
import RPz7_F3P_GammaCell
import RPz7_F3P_LowProjection
import RPz7_F3P_GammaField
import RPz7_F3P_GammaY
import RPz7_F3P_GammaFrame
import RPz7_F3P_Prepared
import RPz7_F3P_PreparedSource
import RPz7_SAP_Immutable
import RPz7_SAP_Discovery
import RPz7_SAP_SameDigest
import RPz7_SAP_Rebind
import RPz7_SAP_Attach
import RPz7_SAF_C_SAP_FinishParsed
import RPz7_SAF_C_SAP_LiteralOutcome
import RPz7_SAF_C_SAF_LiteralOutcome
import RPz7_SAF_C_SAF_PreparedOutcome
import RPz7_SAF_C_SAP_LiteralCont
import RPz7_SAF_C_SAF_LiteralCont
import RPz7_SAF_C_SAF_PreparedCont
import RPz7_SAF_C_SAP_LiteralCaller
import RPz7_SAF_C_SAF_LiteralCaller
import RPz7_SAF_C_SAF_PreparedCaller
import RPz7_TxS_Carriers
import RPz7_Rc4_Model
import RPz7_SAP_FinishConsumer
import RPz7_SAP_FinishParsed
import RPz7_Rc5_Literal
import RPz7_Rc5_Cont
import RPz7_Rc5_Caller
import RPz7_P2P_Caller
import RPz7_FIs_Pair

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_FIp_DotDecode, `RPz7_FIp_NativeDots, `RPz7_FIp_DotsAdapter, `RPz7_FIp_Equality, `RPz7_FIp_SemanticArithmetic, `RPz7_FIp_Install, `RPz7_PAln_JoinedRun, `RPz7_F3L_PreparedPort, `RPz7_PFin_Gates, `RPz7_PFin_Prepared, `RPz7_PFin_Digest, `RPz7_PAln_Oracle, `RPz7_PFin_Attach, `RPz7_SAF_C_Cons_Finish, `RPz7_SAF_C_T2R_Finish, `RPz7_SAF_C_T2R_ContSource, `RPz7_SAP_CurrentNumeric, `RPz7_SAP_NumericFields, `RPz7_SAP_NumericTransport, `RPz7_SAP_LiteralFields, `RPz7_SAF_SavedIdentities, `RPz7_SAF_PreparedPairing, `RPz7_SAF_ReducedLaws, `RPz7_SAF_C_SAP_FinishConsumer, `RPz7_SAF_C_SAP_FinishSaved, `RPz7_SAF_C_SAF_FinishSaved, `RPz7_SAF_C_SAF_FinishPrepared, `RPz7_F3N_WriterReturned, `RPz7_F3L_WriterAlpha, `RPz7_F3L_WriterSemanticAlpha, `RPz7_F3L_WriterCoordinates, `RPz7_F3L_WriterRemaining, `RPz7_F3L_WriterPreparedEq, `RPz7_F3L_WriterBody, `RPz7_F3N_WriterNumeric, `RPz7_F3N_WriterOnRun, `RPz7_F3N_ConsDictionary, `RPz7_F3N_SameOracle, `RPz7_SAP_Cuts, `RPz7_SAP_CanonicalCarrier, `RPz7_SAP_OpeningCuts, `RPz7_SAP_OpeningShape, `RPz7_SAP_SampleCanonical, `RPz7_SAP_SemanticCanonical, `RPz7_SAP_WrapperCanonical, `RPz7_SAP_CircleCanonical, `RPz7_SAP_SemanticCircles, `RPz7_SAP_AlphaTransport, `RPz7_SAP_CoordinateTransport, `RPz7_SAP_PreparedFields, `RPz7_SAP_PrepareOwner, `RPz7_SAP_SaveOnRun, `RPz7_F3P_SemanticY, `RPz7_F3P_GammaCell, `RPz7_F3P_LowProjection, `RPz7_F3P_GammaField, `RPz7_F3P_GammaY, `RPz7_F3P_GammaFrame, `RPz7_F3P_Prepared, `RPz7_F3P_PreparedSource, `RPz7_SAP_Immutable, `RPz7_SAP_Discovery, `RPz7_SAP_SameDigest, `RPz7_SAP_Rebind, `RPz7_SAP_Attach, `RPz7_SAF_C_SAP_FinishParsed, `RPz7_SAF_C_SAP_LiteralOutcome, `RPz7_SAF_C_SAF_LiteralOutcome, `RPz7_SAF_C_SAF_PreparedOutcome, `RPz7_SAF_C_SAP_LiteralCont, `RPz7_SAF_C_SAF_LiteralCont, `RPz7_SAF_C_SAF_PreparedCont, `RPz7_SAF_C_SAP_LiteralCaller, `RPz7_SAF_C_SAF_LiteralCaller, `RPz7_SAF_C_SAF_PreparedCaller, `RPz7_TxS_Carriers, `RPz7_Rc4_Model, `RPz7_SAP_FinishConsumer, `RPz7_SAP_FinishParsed, `RPz7_Rc5_Literal, `RPz7_Rc5_Cont, `RPz7_Rc5_Caller, `RPz7_P2P_Caller, `RPz7_FIs_Pair ]
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
