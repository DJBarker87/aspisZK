import Lean
import RPu_FJo_PairPowers
import RPu_FJo_PairSource
import RPu_FJo_BodyAlpha0
import RPu_FJo_AlphaIndex
import RPu_FJo_WriterAlpha0
import RPu_FJo_ReaderAlpha0
import RPu_FJo_AlphaPersistence
import RPu_FJo_Tx1AlphaSource
import RPu_FJo_Tx1AlphaCanonical
import RPu_FJo_ReaderLiteralAlpha
import RPu_FJo_ReaderQueriesAt
import RPu_FJo_Tx1Geometry
import RPu_FJl_CircleGeometry
import RPu_FJo_GeometryCoordinates
import RPu_FJo_InverseCoordinates
import RPu_FJo_GeometryInverses
import RPu_FJo_RecoveryAt
import RPu_FJp_MatchingAt
import RPu_FJp_Remaining
import RPu_FJp_GlobalOwners
import RPu_FJp_MatchingLaw
import RPu_FJp_RecoveryBranch
import RPu_FJp_AccountJoin
import RPu_FJp_Domination
import RPu_FJp_Mass
import RPu_FJp_Residual
import RPu_FJp_Finish
import RPu_FJp_NativeFirst
import RPu_FJp_NativeReader
import RPu_FJp_NativePair
import RPu_FJp_NativeJoin
import RPu_FJp_Native
import RPu_FJp_NativeBuilder
import RPu_FJp_ConsSecond
import RPu_FJp_NativeLiteral
import RPu_FJp_ActualLiteral
import RPu_FJp_RootBinding
import RPu_FJp_ActualCont
import RPu_FJp_ActualCaller
import RPu_FJp_RetDefinitions
import RPu_FJp_RetPrefix
import RPu_FJp_RetSuffix
import RPu_FJp_Result
import RPu_FJp_RetRc7
import RPu_FJp_Join
import RPu_FJp_CollisionLaw
import RPu_FJp_Cost
import RPu_FJp_ARCore
import RPu_FJp_Observations
import RPu_FJp_FinalObservations
import RPu_FJp_Top
import RPu_FIr_Remaining2
import RPu_FIq_S_ExtractedSemanticRoundCheckedSuccess
import RPu_FIq_S_ExtractedSemanticRoundsCheckedTrace
import RPu_JFv_RawSemanticPolynomialOps
import RPu_JFv_RawExtractedSemanticQM31Ops
import RPu_FIq_S_RawSemanticFieldOwnerAdapter
import RPu_FIq_S_RawSemanticCheckedStepPolynomialAdapter
import RPu_FIq_S_RawSemanticListPolynomialDegree
import RPu_FIq_S_RawSemanticPolynomialDegree28
import RPu_JFv_RawExtractedSemanticCallOpsV20
import RPu_JFv_RawExtractedSemanticCallOpsV23
import RPu_JFv_RawExtractedSemanticBoundaryLoopV7
import RPu_JFv_RawExtractedSemanticValueLoopV1
import RPu_JFv_RawExtractedSemanticPolynomialWrappersV1
import RPu_FIq_S_RawGeneratedSemanticRoundPolynomialAdapter
import RPu_FIq_S_RawActualDecodeKMainAdapter
import RPu_FIq_S_RawActualSemanticRoundCanonicality
import RPu_FIq_S_RawActualEnrichedSemanticRun
import RPu_FIq_S_RawGenericPolynomialSumcheckChain
import RPu_FIq_S_RawActualAnnotatedPolynomialRun
import RPu_FIq_S_RawActualAnnotatedChallengeSequence
import RPu_FIq_Native03
import RPu_FIq_FromFn
import RPu_FIq_Native04
import RPu_FIq_Native05
import RPu_FIq_Native06
import RPu_FIq_Native07
import RPu_FIq_Native08
import RPu_FIq_Native09
import RPu_FIq_Native10
import RPu_FIq_Native11
import RPu_FIq_Native12
import RPu_FIq_CopyPrefix
import RPu_FIq_CopyPatterns
import RPu_FIq_Native13
import RPu_FIq_Native14
import RPu_FIq_Carriers
import RPu_FIq_Terminal
import RPu_FIq_Install
import RPu_FIq_SemanticSource
import RPu_FIq_S_RawActualDecodeKMainReadback
import RPu_FIq_S_RawActualDecodeKMainStrictReadback
import RPu_FIq_S_RawActualDecodeKPayloadBytes
import RPu_FIq_S_R1SourceWideExactCodec
import RPu_FIq_S_RawActualDecodeKRetainedFieldInterpretation
import RPu_FIq_S_RawActualDecodeKStrictChunkBridge
import RPu_FIq_S_RawActualDecodeKTypedCoefficients
import RPu_FIq_S_StrictLowChunkFromTypedDecode
import RPu_FIq_S_RawSemanticTypedPolynomialLift
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPu_FJo_PairPowers, `RPu_FJo_PairSource, `RPu_FJo_BodyAlpha0, `RPu_FJo_AlphaIndex, `RPu_FJo_WriterAlpha0, `RPu_FJo_ReaderAlpha0, `RPu_FJo_AlphaPersistence, `RPu_FJo_Tx1AlphaSource, `RPu_FJo_Tx1AlphaCanonical, `RPu_FJo_ReaderLiteralAlpha, `RPu_FJo_ReaderQueriesAt, `RPu_FJo_Tx1Geometry, `RPu_FJl_CircleGeometry, `RPu_FJo_GeometryCoordinates, `RPu_FJo_InverseCoordinates, `RPu_FJo_GeometryInverses, `RPu_FJo_RecoveryAt, `RPu_FJp_MatchingAt, `RPu_FJp_Remaining, `RPu_FJp_GlobalOwners, `RPu_FJp_MatchingLaw, `RPu_FJp_RecoveryBranch, `RPu_FJp_AccountJoin, `RPu_FJp_Domination, `RPu_FJp_Mass, `RPu_FJp_Residual, `RPu_FJp_Finish, `RPu_FJp_NativeFirst, `RPu_FJp_NativeReader, `RPu_FJp_NativePair, `RPu_FJp_NativeJoin, `RPu_FJp_Native, `RPu_FJp_NativeBuilder, `RPu_FJp_ConsSecond, `RPu_FJp_NativeLiteral, `RPu_FJp_ActualLiteral, `RPu_FJp_RootBinding, `RPu_FJp_ActualCont, `RPu_FJp_ActualCaller, `RPu_FJp_RetDefinitions, `RPu_FJp_RetPrefix, `RPu_FJp_RetSuffix, `RPu_FJp_Result, `RPu_FJp_RetRc7, `RPu_FJp_Join, `RPu_FJp_CollisionLaw, `RPu_FJp_Cost, `RPu_FJp_ARCore, `RPu_FJp_Observations, `RPu_FJp_FinalObservations, `RPu_FJp_Top, `RPu_FIr_Remaining2, `RPu_FIq_S_ExtractedSemanticRoundCheckedSuccess, `RPu_FIq_S_ExtractedSemanticRoundsCheckedTrace, `RPu_JFv_RawSemanticPolynomialOps, `RPu_JFv_RawExtractedSemanticQM31Ops, `RPu_FIq_S_RawSemanticFieldOwnerAdapter, `RPu_FIq_S_RawSemanticCheckedStepPolynomialAdapter, `RPu_FIq_S_RawSemanticListPolynomialDegree, `RPu_FIq_S_RawSemanticPolynomialDegree28, `RPu_JFv_RawExtractedSemanticCallOpsV20, `RPu_JFv_RawExtractedSemanticCallOpsV23, `RPu_JFv_RawExtractedSemanticBoundaryLoopV7, `RPu_JFv_RawExtractedSemanticValueLoopV1, `RPu_JFv_RawExtractedSemanticPolynomialWrappersV1, `RPu_FIq_S_RawGeneratedSemanticRoundPolynomialAdapter, `RPu_FIq_S_RawActualDecodeKMainAdapter, `RPu_FIq_S_RawActualSemanticRoundCanonicality, `RPu_FIq_S_RawActualEnrichedSemanticRun, `RPu_FIq_S_RawGenericPolynomialSumcheckChain, `RPu_FIq_S_RawActualAnnotatedPolynomialRun, `RPu_FIq_S_RawActualAnnotatedChallengeSequence, `RPu_FIq_Native03, `RPu_FIq_FromFn, `RPu_FIq_Native04, `RPu_FIq_Native05, `RPu_FIq_Native06, `RPu_FIq_Native07, `RPu_FIq_Native08, `RPu_FIq_Native09, `RPu_FIq_Native10, `RPu_FIq_Native11, `RPu_FIq_Native12, `RPu_FIq_CopyPrefix, `RPu_FIq_CopyPatterns, `RPu_FIq_Native13, `RPu_FIq_Native14, `RPu_FIq_Carriers, `RPu_FIq_Terminal, `RPu_FIq_Install, `RPu_FIq_SemanticSource, `RPu_FIq_S_RawActualDecodeKMainReadback, `RPu_FIq_S_RawActualDecodeKMainStrictReadback, `RPu_FIq_S_RawActualDecodeKPayloadBytes, `RPu_FIq_S_R1SourceWideExactCodec, `RPu_FIq_S_RawActualDecodeKRetainedFieldInterpretation, `RPu_FIq_S_RawActualDecodeKStrictChunkBridge, `RPu_FIq_S_RawActualDecodeKTypedCoefficients, `RPu_FIq_S_StrictLowChunkFromTypedDecode, `RPu_FIq_S_RawSemanticTypedPolynomialLift ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPU_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPU_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPU_AUDIT_COMPLETE declarations={count} modules={selected.size}"
