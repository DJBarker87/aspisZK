import Lean
import RPz7_PAln_OpeningReach
import RPz7_PAln_OpeningStages
import RPz7_PAln_BothBuffers
import RPz7_PSem_Root
import RPz7_PSem_RoundCalls
import RPz7_PSem_SemanticTrace
import RPz7_PAln_FullCut
import RPz7_PAln_CurrentPhysical
import RPz7_F3J_OpeningPayloads
import RPz7_F3K_OpeningSpine
import RPz7_F3K_SourceQueryDecode
import RPz7_F3K_PreparedSourceFields
import RPz7_GExp_Association
import RPz7_GExp_AssociationTactic
import RPz7_GExp_SampleBlockAssociation
import RPz7_GExp_SemanticValidatedAssociation
import RPz7_GExp_Begin13Association
import RPz7_GExp_Begin9Association
import RPz7_GExp_Begin5Association
import RPz7_GExp_BeginAssociation
import RPz7_GExp_NewTranscriptAssociation
import RPz7_GExp_PublicTranscriptAssociation
import RPz7_GExp_RoundStepAssociation
import RPz7_GExp_RoundsAssociation
import RPz7_GExp_CircleValidatedAssociation
import RPz7_GExp_FinishAssociation
import RPz7_GExp_VerifyAssociation
import RPz7_GExp_PreparedNewAssociation
import RPz7_GExp_PreparedAbsorbAssociation
import RPz7_GExp_PreparedBlockAssociation
import RPz7_GExp_PreparedScalarAssociation
import RPz7_GExp_PreparedScalar_kAssociation
import RPz7_GExp_PreparedQueriesAssociation
import RPz7_GExp_PreparedPreparationAssociation
import RPz7_GExp_PrepareAssociation
import RPz7_SdkD_PrepareTransport
import RPz7_GExp_InstalledPrepare
import RPz7_S1PrepareBudgetCoreV1
import RPz7_S1PrepareBudgetTacticV1
import RPz7_S1SemanticBudgetV1
import RPz7_S1PreparedBudgetV1
import RPz7_S1CurrentPrepareBudgetV1
import RPz7_GExp_QueryBudget
import RPz7_Tx2I_Install
import RPz7_Tx2I_Cuts
import RPz7_Tx2I_Finish
import RPz7_Op3I_Accepted
import RPz7_Tx2I_Accepted
import RPz7_Op5T_Install
import RPz7_Op5T_Concrete
import RPz7_SdkC_BatchSource
import RPz7_Op5C_RejectedMarks
import RPz7_Op3I_Nonvacuity
import RPz7_Op3I_Witness
import RPz7_Tx2I_Nonvacuity
import RPz7_Tx2I_Witness
import RPz7_Op5T_Marks
import RPz7_SdkD_Control
import RPz7_SdkD_First
import RPz7_GExp_FirstCode
import RPz7_F3K_CheckpointPreparedFields
import RPz7_F3L_SourceNumeric
import RPz7_F3L_SourceAlphaIndex
import RPz7_F3L_RhoCanonical
import RPz7_F3K_OpeningQuery
import RPz7_F3L_PreparePort
import RPz7_F3L_WriterSourceScalar
import RPz7_F3L_WriterPreparedScalar
import RPz7_F3L_SourcePrepared
import RPz7_F3L_SourceAlphaValues
import RPz7_F3K_CheckpointQueryNumeric
import RPz7_F3L_PreparedQueryPort
import RPz7_F3L_PreparedModelSix
import RPz7_F3L_PreparedRemaining
import RPz7_F3M_PreparedRemaining
import RPz7_F3N_PreparedClaim
import RPz7_AspisR1CircleSampleWrapper_FunsExternal
import RPz7_AspisR1CircleSampleWrapper_Funs
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleEmittedWrapperLaw
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualSamplerCanonicalV1
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualSecureBridgeV1
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackResultV4
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackCoordinatesV1
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackCircleV2

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_PAln_OpeningReach, `RPz7_PAln_OpeningStages, `RPz7_PAln_BothBuffers, `RPz7_PSem_Root, `RPz7_PSem_RoundCalls, `RPz7_PSem_SemanticTrace, `RPz7_PAln_FullCut, `RPz7_PAln_CurrentPhysical, `RPz7_F3J_OpeningPayloads, `RPz7_F3K_OpeningSpine, `RPz7_F3K_SourceQueryDecode, `RPz7_F3K_PreparedSourceFields, `RPz7_GExp_Association, `RPz7_GExp_AssociationTactic, `RPz7_GExp_SampleBlockAssociation, `RPz7_GExp_SemanticValidatedAssociation, `RPz7_GExp_Begin13Association, `RPz7_GExp_Begin9Association, `RPz7_GExp_Begin5Association, `RPz7_GExp_BeginAssociation, `RPz7_GExp_NewTranscriptAssociation, `RPz7_GExp_PublicTranscriptAssociation, `RPz7_GExp_RoundStepAssociation, `RPz7_GExp_RoundsAssociation, `RPz7_GExp_CircleValidatedAssociation, `RPz7_GExp_FinishAssociation, `RPz7_GExp_VerifyAssociation, `RPz7_GExp_PreparedNewAssociation, `RPz7_GExp_PreparedAbsorbAssociation, `RPz7_GExp_PreparedBlockAssociation, `RPz7_GExp_PreparedScalarAssociation, `RPz7_GExp_PreparedScalar_kAssociation, `RPz7_GExp_PreparedQueriesAssociation, `RPz7_GExp_PreparedPreparationAssociation, `RPz7_GExp_PrepareAssociation, `RPz7_SdkD_PrepareTransport, `RPz7_GExp_InstalledPrepare, `RPz7_S1PrepareBudgetCoreV1, `RPz7_S1PrepareBudgetTacticV1, `RPz7_S1SemanticBudgetV1, `RPz7_S1PreparedBudgetV1, `RPz7_S1CurrentPrepareBudgetV1, `RPz7_GExp_QueryBudget, `RPz7_Tx2I_Install, `RPz7_Tx2I_Cuts, `RPz7_Tx2I_Finish, `RPz7_Op3I_Accepted, `RPz7_Tx2I_Accepted, `RPz7_Op5T_Install, `RPz7_Op5T_Concrete, `RPz7_SdkC_BatchSource, `RPz7_Op5C_RejectedMarks, `RPz7_Op3I_Nonvacuity, `RPz7_Op3I_Witness, `RPz7_Tx2I_Nonvacuity, `RPz7_Tx2I_Witness, `RPz7_Op5T_Marks, `RPz7_SdkD_Control, `RPz7_SdkD_First, `RPz7_GExp_FirstCode, `RPz7_F3K_CheckpointPreparedFields, `RPz7_F3L_SourceNumeric, `RPz7_F3L_SourceAlphaIndex, `RPz7_F3L_RhoCanonical, `RPz7_F3K_OpeningQuery, `RPz7_F3L_PreparePort, `RPz7_F3L_WriterSourceScalar, `RPz7_F3L_WriterPreparedScalar, `RPz7_F3L_SourcePrepared, `RPz7_F3L_SourceAlphaValues, `RPz7_F3K_CheckpointQueryNumeric, `RPz7_F3L_PreparedQueryPort, `RPz7_F3L_PreparedModelSix, `RPz7_F3L_PreparedRemaining, `RPz7_F3M_PreparedRemaining, `RPz7_F3N_PreparedClaim, `RPz7_AspisR1CircleSampleWrapper_FunsExternal, `RPz7_AspisR1CircleSampleWrapper_Funs, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleEmittedWrapperLaw, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualSamplerCanonicalV1, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualSecureBridgeV1, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackResultV4, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackCoordinatesV1, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackCircleV2 ]
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
