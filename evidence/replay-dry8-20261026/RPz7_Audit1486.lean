import Lean
import RPz7_F3J_OpeningFrame
import RPz7_F3J_LengthFrame
import RPz7_F3J_QueryJoin
import RPz7_F3J_QuerySource
import RPz7_F3J_QuerySelection
import RPz7_F3K_ArrayFacts
import RPz7_F3K_ArrayValues
import RPz7_F3K_QueryChain
import RPz7_F3K_QueryValues
import RPz7_F3K_QueryDecoderSource
import RPz7_F3K_QueryWords
import RPz7_F3K_WordCodec
import RPz7_F3K_LimbBytes
import RPz7_PAln_InactiveDecode
import RPz7_F3K_WideEncoding
import RPz7_F3K_InactiveCodec
import RPz7_F3K_InactivePhysical
import RPz7_F3M_InactiveCanonical
import RPz7_PAln_Borrowed
import RPz7_F3M_PreparedClaim
import RPz7_F3M_ClaimTerms
import RPz7_F3M_ClaimExpansion
import RPz7_F3M_ClaimNumeric
import RPz7_F3N_ClaimShape
import RPz7_F3N_ClaimPolynomial
import RPz7_F3N_OrderedSum
import RPz7_F3N_ClaimRowSum
import RPz7_F3N_ClaimCell
import RPz7_F3N_OriginalClaim
import RPz7_F3L_EraseIndex
import RPz7_F3L_MatchingFromEntries
import RPz7_F3J_SamplerCompose
import RPz7_F3K_SamplerOne
import RPz7_F3J_SamplerStep
import RPz7_F3K_SamplerProtocol
import RPz7_F3K_SamplerIndex
import RPz7_F3L_SamplerAt
import RPz7_F3L_GammaMeaning
import RPz7_F3J_OpeningSampler
import RPz7_F3L_GammaChallenge
import RPz7_F3J_OpeningCode
import RPz7_F3K_AbsorbCode
import RPz7_AuS1_Trace
import RPz7_F3K_CodeStep
import RPz7_F3K_QueryCode
import RPz7_F3K_QueryScanCall
import RPz7_F3K_QueryIndex
import RPz7_F3K_QueryScanStep
import RPz7_F3K_QueryScanLast
import RPz7_F3K_QueryDriverModel
import RPz7_F3K_ConcreteDecode
import RPz7_F3J_QueryAbsorber
import RPz7_F3K_QuerySamplerOutput
import RPz7_F3K_QueryAddress
import RPz7_F3K_QueryRowOutput
import RPz7_F3K_QueryFull
import RPz7_F3J_ScalarCode
import RPz7_F3J_OpeningJoin
import RPz7_F3K_ScalarJoin
import RPz7_F3K_RhoJoin
import RPz7_F3K_PayloadFits
import RPz7_F3K_OpeningCalls
import RPz7_F3L_SamplingSlots
import RPz7_F3L_ClosedGamma
import RPz7_F3L_GammaEntry
import RPz7_F3L_OrdinaryMeaning
import RPz7_F3L_OrdinaryChallenge
import RPz7_F3L_ClosedOrdinary
import RPz7_F3L_OrdinaryEntry
import RPz7_F3K_ScalarOne
import RPz7_F3K_OpeningPair27
import RPz7_F3L_OpeningPairValues
import RPz7_F3L_OpeningAlphaValues
import RPz7_F3L_OpeningDataFields
import RPz7_F3L_RhoMeaning
import RPz7_F3L_RhoChallenge
import RPz7_F3L_RhoEntry
import RPz7_F3K_OpeningPair29
import RPz7_F3K_OpeningFirst4
import RPz7_F3K_QueryOne
import RPz7_F3L_OpeningLateEntries
import RPz7_F3L_OpeningInputLate
import RPz7_PAln_RootConvert
import RPz7_PAln_Row30Source

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_F3J_OpeningFrame, `RPz7_F3J_LengthFrame, `RPz7_F3J_QueryJoin, `RPz7_F3J_QuerySource, `RPz7_F3J_QuerySelection, `RPz7_F3K_ArrayFacts, `RPz7_F3K_ArrayValues, `RPz7_F3K_QueryChain, `RPz7_F3K_QueryValues, `RPz7_F3K_QueryDecoderSource, `RPz7_F3K_QueryWords, `RPz7_F3K_WordCodec, `RPz7_F3K_LimbBytes, `RPz7_PAln_InactiveDecode, `RPz7_F3K_WideEncoding, `RPz7_F3K_InactiveCodec, `RPz7_F3K_InactivePhysical, `RPz7_F3M_InactiveCanonical, `RPz7_PAln_Borrowed, `RPz7_F3M_PreparedClaim, `RPz7_F3M_ClaimTerms, `RPz7_F3M_ClaimExpansion, `RPz7_F3M_ClaimNumeric, `RPz7_F3N_ClaimShape, `RPz7_F3N_ClaimPolynomial, `RPz7_F3N_OrderedSum, `RPz7_F3N_ClaimRowSum, `RPz7_F3N_ClaimCell, `RPz7_F3N_OriginalClaim, `RPz7_F3L_EraseIndex, `RPz7_F3L_MatchingFromEntries, `RPz7_F3J_SamplerCompose, `RPz7_F3K_SamplerOne, `RPz7_F3J_SamplerStep, `RPz7_F3K_SamplerProtocol, `RPz7_F3K_SamplerIndex, `RPz7_F3L_SamplerAt, `RPz7_F3L_GammaMeaning, `RPz7_F3J_OpeningSampler, `RPz7_F3L_GammaChallenge, `RPz7_F3J_OpeningCode, `RPz7_F3K_AbsorbCode, `RPz7_AuS1_Trace, `RPz7_F3K_CodeStep, `RPz7_F3K_QueryCode, `RPz7_F3K_QueryScanCall, `RPz7_F3K_QueryIndex, `RPz7_F3K_QueryScanStep, `RPz7_F3K_QueryScanLast, `RPz7_F3K_QueryDriverModel, `RPz7_F3K_ConcreteDecode, `RPz7_F3J_QueryAbsorber, `RPz7_F3K_QuerySamplerOutput, `RPz7_F3K_QueryAddress, `RPz7_F3K_QueryRowOutput, `RPz7_F3K_QueryFull, `RPz7_F3J_ScalarCode, `RPz7_F3J_OpeningJoin, `RPz7_F3K_ScalarJoin, `RPz7_F3K_RhoJoin, `RPz7_F3K_PayloadFits, `RPz7_F3K_OpeningCalls, `RPz7_F3L_SamplingSlots, `RPz7_F3L_ClosedGamma, `RPz7_F3L_GammaEntry, `RPz7_F3L_OrdinaryMeaning, `RPz7_F3L_OrdinaryChallenge, `RPz7_F3L_ClosedOrdinary, `RPz7_F3L_OrdinaryEntry, `RPz7_F3K_ScalarOne, `RPz7_F3K_OpeningPair27, `RPz7_F3L_OpeningPairValues, `RPz7_F3L_OpeningAlphaValues, `RPz7_F3L_OpeningDataFields, `RPz7_F3L_RhoMeaning, `RPz7_F3L_RhoChallenge, `RPz7_F3L_RhoEntry, `RPz7_F3K_OpeningPair29, `RPz7_F3K_OpeningFirst4, `RPz7_F3K_QueryOne, `RPz7_F3L_OpeningLateEntries, `RPz7_F3L_OpeningInputLate, `RPz7_PAln_RootConvert, `RPz7_PAln_Row30Source ]
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
