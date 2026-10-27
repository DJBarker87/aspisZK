import Lean
import RPz7_Rc5_Extract
import RPz7_FIs_P2P_Source
import RPz7_Rc5_Source
import RPz7_Rc5_Close
import RPz7_CPH_Trace
import RPz7_CPH_Recorder
import RPz7_Rc2_Top
import RPz7_CPH_Extract
import RPz7_CPH_Rc2Source
import RPz7_CPH_Close
import RPz7_CPH_Pair
import RPz7_CPH_Protection
import RPz7_CPG_Pair
import RPz7_Hiq_RecordedJoint
import RPz7_Hiq_RecordedBudget
import RPz7_F3T_Numeric
import RPz7_F3T_AccountCharge
import RPz7_F3T_AccountSource
import RPz7_F3T_Installed
import RPz7_F3T_ByteCarrier
import RPz7_F3T_Carried
import RPz7_F3T_CanonicalJoin
import RPz7_F3T_ByteTransport
import RPz7_F3T_Runtime
import RPz7_F3T_RuntimeBound
import RPz7_F3T_Combined
import RPz7_F3T_Conditional
import RPz7_F3T_InstalledRecovered
import RPz7_F3T_SourceCost
import RPz7_F3T_ConditionalSum
import RPz7_CPG_Account
import RPz7_F3T_ConditionalClaims
import RPz7_FIs_Rc7_Native
import RPz7_FIs_P2P_R6Result
import RPz7_P2P_NativeSelection
import RPz7_P2P_Charge
import RPz7_FIs_P2P_Release
import RPz7_F3U_SourceInputs
import RPz7_F3U_PairInputs
import RPz7_F3U_ReifyFirst
import RPz7_F3U_AsSliceBytes
import RPz7_F3U_AllWorldMachine
import RPz7_F3U_Rehash
import RPz7_F3V_OracleDictionary
import RPz7_F3U_RehashBind
import RPz7_F3V_SampleBlock
import RPz7_F3V_SemanticValidated
import RPz7_F3V_Begin13
import RPz7_F3V_Begin9
import RPz7_F3V_Begin5
import RPz7_F3V_Begin
import RPz7_F3V_RoundStep
import RPz7_F3V_Rounds
import RPz7_F3V_CircleValidated
import RPz7_F3V_SemanticFinish
import RPz7_F3U_RehashInit
import RPz7_F3U_RehashPublic
import RPz7_F3V_SemanticVerify
import RPz7_F3V_CurrentSemantic
import RPz7_F3V_RehashCongr
import RPz7_F3V_TranscriptNew
import RPz7_F3V_TranscriptAbsorb
import RPz7_F3V_TranscriptBlock
import RPz7_F3V_Scalar
import RPz7_F3V_Rho
import RPz7_F3V_Queries
import RPz7_F3V_PreparedGeneric
import RPz7_F3V_ClaimDictionary
import RPz7_F3V_ClaimPublic
import RPz7_F3V_ClosedPreparation
import RPz7_F3V_Preparation
import RPz7_F3V_SdkPreparation
import RPz7_F3V_LoweredPreparation
import RPz7_F3S_BatchDictionary
import RPz7_F3V_BatchDictionary
import RPz7_F3V_FirstTemplate
import RPz7_F3U_FirstSkeleton
import RPz7_F3U_FirstInstances
import RPz7_F3V_FirstInstance
import RPz7_F3V_FirstCode
import RPz7_F3V_AllWorldFirst
import RPz7_F3U_SecondSkeleton
import RPz7_F3U_SecondInstances
import RPz7_PhaseConsumers

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_Rc5_Extract, `RPz7_FIs_P2P_Source, `RPz7_Rc5_Source, `RPz7_Rc5_Close, `RPz7_CPH_Trace, `RPz7_CPH_Recorder, `RPz7_Rc2_Top, `RPz7_CPH_Extract, `RPz7_CPH_Rc2Source, `RPz7_CPH_Close, `RPz7_CPH_Pair, `RPz7_CPH_Protection, `RPz7_CPG_Pair, `RPz7_Hiq_RecordedJoint, `RPz7_Hiq_RecordedBudget, `RPz7_F3T_Numeric, `RPz7_F3T_AccountCharge, `RPz7_F3T_AccountSource, `RPz7_F3T_Installed, `RPz7_F3T_ByteCarrier, `RPz7_F3T_Carried, `RPz7_F3T_CanonicalJoin, `RPz7_F3T_ByteTransport, `RPz7_F3T_Runtime, `RPz7_F3T_RuntimeBound, `RPz7_F3T_Combined, `RPz7_F3T_Conditional, `RPz7_F3T_InstalledRecovered, `RPz7_F3T_SourceCost, `RPz7_F3T_ConditionalSum, `RPz7_CPG_Account, `RPz7_F3T_ConditionalClaims, `RPz7_FIs_Rc7_Native, `RPz7_FIs_P2P_R6Result, `RPz7_P2P_NativeSelection, `RPz7_P2P_Charge, `RPz7_FIs_P2P_Release, `RPz7_F3U_SourceInputs, `RPz7_F3U_PairInputs, `RPz7_F3U_ReifyFirst, `RPz7_F3U_AsSliceBytes, `RPz7_F3U_AllWorldMachine, `RPz7_F3U_Rehash, `RPz7_F3V_OracleDictionary, `RPz7_F3U_RehashBind, `RPz7_F3V_SampleBlock, `RPz7_F3V_SemanticValidated, `RPz7_F3V_Begin13, `RPz7_F3V_Begin9, `RPz7_F3V_Begin5, `RPz7_F3V_Begin, `RPz7_F3V_RoundStep, `RPz7_F3V_Rounds, `RPz7_F3V_CircleValidated, `RPz7_F3V_SemanticFinish, `RPz7_F3U_RehashInit, `RPz7_F3U_RehashPublic, `RPz7_F3V_SemanticVerify, `RPz7_F3V_CurrentSemantic, `RPz7_F3V_RehashCongr, `RPz7_F3V_TranscriptNew, `RPz7_F3V_TranscriptAbsorb, `RPz7_F3V_TranscriptBlock, `RPz7_F3V_Scalar, `RPz7_F3V_Rho, `RPz7_F3V_Queries, `RPz7_F3V_PreparedGeneric, `RPz7_F3V_ClaimDictionary, `RPz7_F3V_ClaimPublic, `RPz7_F3V_ClosedPreparation, `RPz7_F3V_Preparation, `RPz7_F3V_SdkPreparation, `RPz7_F3V_LoweredPreparation, `RPz7_F3S_BatchDictionary, `RPz7_F3V_BatchDictionary, `RPz7_F3V_FirstTemplate, `RPz7_F3U_FirstSkeleton, `RPz7_F3U_FirstInstances, `RPz7_F3V_FirstInstance, `RPz7_F3V_FirstCode, `RPz7_F3V_AllWorldFirst, `RPz7_F3U_SecondSkeleton, `RPz7_F3U_SecondInstances, `RPz7_PhaseConsumers ]
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
