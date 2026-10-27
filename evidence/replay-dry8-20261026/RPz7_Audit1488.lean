import Lean
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyV2
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyUnconditionalV1
import RPz7_R4TransportCircleCoordinates
import RPz7_F3M_CircleSource
import RPz7_F3M_CircleSourceCall
import RPz7_F3M_CircleMeaning
import RPz7_F3M_CircleFirstModel
import RPz7_F3M_CircleSecondModel
import RPz7_F3M_CircleParameters
import RPz7_F3N_CircleCoordinates
import RPz7_F3N_CircleProjection
import RPz7_F3N_CoordinateShape
import RPz7_F3N_PreparedCoordinates
import RPz7_F3N_Prepared
import RPz7_F3N_SelectedScalar
import RPz7_F3N_SelectedDispatch
import RPz7_F3N_PreparedCells
import RPz7_F3P_DecodeCells
import RPz7_F3P_DecodeCellTrace
import RPz7_PAln_FieldRead
import RPz7_PAln_LowRead
import RPz7_F3P_DecodeLimbMeaning
import RPz7_F3P_LowLimbMeaning
import RPz7_F3P_StrictLowParser
import RPz7_F3P_TraceParsed
import RPz7_F3P_TracePayload
import RPz7_F3P_DecodeNumeric
import RPz7_F3P_LowDecodeInjective
import RPz7_PAln_Transcript
import RPz7_ExtractedPrefixTypedFullCurrent
import RPz7_ExtractedSourceFull25Typed
import RPz7_RawSourceLiteralInitialCall
import RPz7_PAln_SemanticRead
import RPz7_PAln_TypedRows
import RPz7_PAln_AlignedRead
import RPz7_F3P_AlignedRow
import RPz7_F3P_InputY
import RPz7_F3P_YCells
import RPz7_PAln_SequenceRead
import RPz7_PAln_SemanticLayout
import RPz7_PAln_CircleDecode
import RPz7_F3P_CircleCell
import RPz7_F3P_LowCellRead
import RPz7_F3P_DecodeCircleCell
import RPz7_F3P_ArrayIndex
import RPz7_F3P_ThreeRows
import RPz7_F3P_DecodeCircleIndex
import RPz7_F3P_ClaimsCells
import RPz7_F3M_WideMeaning
import RPz7_F3M_InactiveReader
import RPz7_F3M_InactivePhysicalMeaning
import RPz7_F3M_InactiveRow28
import RPz7_F3M_InactiveInput
import RPz7_F3J_BlockCode
import RPz7_F3J_BlockCodeValue
import RPz7_PAln_CircleCalls
import RPz7_F3J_CircleCode
import RPz7_F3J_BlockSampler
import RPz7_F3J_ReseedSampler
import RPz7_F3J_RowBindings
import RPz7_F3J_RecordPayload
import RPz7_F3J_CircleJoin
import RPz7_F3M_CircleValues
import RPz7_F3M_CircleEntries
import RPz7_F3M_CircleReader
import RPz7_F3M_CirclePrefixReader
import RPz7_Op5T_Accepted
import RPz7_Op5T_Cuts
import RPz7_Op5T_SamePair
import RPz7_SdkC_BatchPair
import RPz7_Op5I_EventCounterexample
import RPz7_Op5I_AcceptedCarrierCounterexample
import RPz7_Op5T_P6
import RPz7_Op5T_NativeAuth
import RPz7_Op5T_SelectedPaths
import RPz7_SdkC_Authentication
import RPz7_SdkC_FirstAuthentication
import RPz7_SdkD_QueryBinding
import RPz7_Op5T_OuterAccepted
import RPz7_Op5T_Schedule
import RPz7_Op5T_NativeSchedule
import RPz7_Op5T_Scheduled
import RPz7_Op5T_D189
import RPz7_Op5T_Claims

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyV2, `RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyUnconditionalV1, `RPz7_R4TransportCircleCoordinates, `RPz7_F3M_CircleSource, `RPz7_F3M_CircleSourceCall, `RPz7_F3M_CircleMeaning, `RPz7_F3M_CircleFirstModel, `RPz7_F3M_CircleSecondModel, `RPz7_F3M_CircleParameters, `RPz7_F3N_CircleCoordinates, `RPz7_F3N_CircleProjection, `RPz7_F3N_CoordinateShape, `RPz7_F3N_PreparedCoordinates, `RPz7_F3N_Prepared, `RPz7_F3N_SelectedScalar, `RPz7_F3N_SelectedDispatch, `RPz7_F3N_PreparedCells, `RPz7_F3P_DecodeCells, `RPz7_F3P_DecodeCellTrace, `RPz7_PAln_FieldRead, `RPz7_PAln_LowRead, `RPz7_F3P_DecodeLimbMeaning, `RPz7_F3P_LowLimbMeaning, `RPz7_F3P_StrictLowParser, `RPz7_F3P_TraceParsed, `RPz7_F3P_TracePayload, `RPz7_F3P_DecodeNumeric, `RPz7_F3P_LowDecodeInjective, `RPz7_PAln_Transcript, `RPz7_ExtractedPrefixTypedFullCurrent, `RPz7_ExtractedSourceFull25Typed, `RPz7_RawSourceLiteralInitialCall, `RPz7_PAln_SemanticRead, `RPz7_PAln_TypedRows, `RPz7_PAln_AlignedRead, `RPz7_F3P_AlignedRow, `RPz7_F3P_InputY, `RPz7_F3P_YCells, `RPz7_PAln_SequenceRead, `RPz7_PAln_SemanticLayout, `RPz7_PAln_CircleDecode, `RPz7_F3P_CircleCell, `RPz7_F3P_LowCellRead, `RPz7_F3P_DecodeCircleCell, `RPz7_F3P_ArrayIndex, `RPz7_F3P_ThreeRows, `RPz7_F3P_DecodeCircleIndex, `RPz7_F3P_ClaimsCells, `RPz7_F3M_WideMeaning, `RPz7_F3M_InactiveReader, `RPz7_F3M_InactivePhysicalMeaning, `RPz7_F3M_InactiveRow28, `RPz7_F3M_InactiveInput, `RPz7_F3J_BlockCode, `RPz7_F3J_BlockCodeValue, `RPz7_PAln_CircleCalls, `RPz7_F3J_CircleCode, `RPz7_F3J_BlockSampler, `RPz7_F3J_ReseedSampler, `RPz7_F3J_RowBindings, `RPz7_F3J_RecordPayload, `RPz7_F3J_CircleJoin, `RPz7_F3M_CircleValues, `RPz7_F3M_CircleEntries, `RPz7_F3M_CircleReader, `RPz7_F3M_CirclePrefixReader, `RPz7_Op5T_Accepted, `RPz7_Op5T_Cuts, `RPz7_Op5T_SamePair, `RPz7_SdkC_BatchPair, `RPz7_Op5I_EventCounterexample, `RPz7_Op5I_AcceptedCarrierCounterexample, `RPz7_Op5T_P6, `RPz7_Op5T_NativeAuth, `RPz7_Op5T_SelectedPaths, `RPz7_SdkC_Authentication, `RPz7_SdkC_FirstAuthentication, `RPz7_SdkD_QueryBinding, `RPz7_Op5T_OuterAccepted, `RPz7_Op5T_Schedule, `RPz7_Op5T_NativeSchedule, `RPz7_Op5T_Scheduled, `RPz7_Op5T_D189, `RPz7_Op5T_Claims ]
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
