import Lean
import R1UnifiedOpeningLaw
import R1QueryBackgroundLaw
import R1UnifiedQueryLaw
import R1JointUnifiedLaw
import R1JointUnifiedBound
import R1UnifiedDecoderBound
import R1UnifiedCausalBound
import R1UnifiedQueryDensity
import R1SubfieldBatchStage2
import R1ResidualBatch
import R1QueryAccumulator
import R1GenericPackBasis
import R1ConcretePackBasis
import R1GenericProgramRenameMass
import R1ProgramSamplerMap
import R1GenericNoHit
import R1GenericNoHitFS2
import OracleProgramRecording
import AllAddressFiatShamirOutside
import AdaptiveStatementFiatShamir
import BackgroundAddressMap
import BackgroundCanonicalLabels
import UnifiedDecoderCanonical
import PartialAddressTrace
import BackgroundAddressFollow
import BackgroundAddressRestriction
import R1CanonicalAddressEmbedding
import CanonicalRawTrace
import PartialAddressImage
import RawBoundedTrace
import RawBackgroundCompletion
import RawUnifiedDecoder
import R1SemanticBudget
import ExtractorPowComplexity
import CantorZassenhausPair
import CantorZassenhausSplit
import FiniteFieldModularPower
import CantorZassenhausFastTrial
import CantorZassenhausRetries
import R1TypedPrefixParser
import R1SemanticPrefixCodec
import R1GenericNoHitIndex
import PoseidonMap
import R1PoseidonMap
import R1NoteHashMap
import R1AppendBindingMap
import R1SpendRelationMap
import R1SpendBaseDescent
import R1TraceSpendWitness
import R1InputWitness
import R1AppendSemantics
import R1SpendRelationExtraction
import R0P.MaskSemantics
import R0P.MaskPrefix
import R0P.MaskNoHit
import R1SemanticHit
import R0P.MaskEarly
import RawTranscriptFrameBytes
import OracleProgramReplay
import GSInterpolationBudget
import FiniteFieldCompleteRootCertificate
import FiniteFieldNormalizedRootFactor
import RRRootDescent
import RRChildNormalization
import RRActualTaylorSubstitutionV3
import RRActualBivariateTaylorBridgeV8
import RRDiagonalSubstitutionExpansionV27
import RRChildSliceTaylorV4
import RRRootMultiplicityTaylorV3
import RRChildSliceMultiplicityV3
import RRActualFixedParentConvolutionV7
import RRNormalizedChildSlice
import RRActualNormalizedTransition
import RRDenseCoeffVectorV6
import RRVectorRowBridgeV12
import RRVectorRowBridgeV14
import RRFiniteCoeffScannerV9
import RRVectorRowNonzeroV5
import RRVectorActualScannerV2
import RRScannedNormalizedTransition
import RRVectorNormalizedRowsV12
import RRVectorNormalizedStateV4
import RRSubstitutionTailBound
import RRVectorNormalizedCompleteV3
import RRSubstitutionOuterDegreeBound
import RRInitialFullRowsScanFacts
import RRPrefixCollector
import RRVectorPolynomialReconstructionV9
import RRRuntimeNormalizedChildReconstruction
import RRConcreteChildModel
import RRBoundedSliceScannerV5
import RRSiblingMultiplicityMassV2
import GSRootCandidateContract
import FiniteOptionSamplerComposition
import GSDecoderTapeReindex
import M31AcceptFiber
import FSRetryOutputUniformity
import M31RetryOutputFiber
import M31RejectFiber
import M31RetryAbortFiber

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1UnifiedOpeningLaw, `R1QueryBackgroundLaw, `R1UnifiedQueryLaw, `R1JointUnifiedLaw, `R1JointUnifiedBound, `R1UnifiedDecoderBound, `R1UnifiedCausalBound, `R1UnifiedQueryDensity, `R1SubfieldBatchStage2, `R1ResidualBatch, `R1QueryAccumulator, `R1GenericPackBasis, `R1ConcretePackBasis, `R1GenericProgramRenameMass, `R1ProgramSamplerMap, `R1GenericNoHit, `R1GenericNoHitFS2, `OracleProgramRecording, `AllAddressFiatShamirOutside, `AdaptiveStatementFiatShamir, `BackgroundAddressMap, `BackgroundCanonicalLabels, `UnifiedDecoderCanonical, `PartialAddressTrace, `BackgroundAddressFollow, `BackgroundAddressRestriction, `R1CanonicalAddressEmbedding, `CanonicalRawTrace, `PartialAddressImage, `RawBoundedTrace, `RawBackgroundCompletion, `RawUnifiedDecoder, `R1SemanticBudget, `ExtractorPowComplexity, `CantorZassenhausPair, `CantorZassenhausSplit, `FiniteFieldModularPower, `CantorZassenhausFastTrial, `CantorZassenhausRetries, `R1TypedPrefixParser, `R1SemanticPrefixCodec, `R1GenericNoHitIndex, `PoseidonMap, `R1PoseidonMap, `R1NoteHashMap, `R1AppendBindingMap, `R1SpendRelationMap, `R1SpendBaseDescent, `R1TraceSpendWitness, `R1InputWitness, `R1AppendSemantics, `R1SpendRelationExtraction, `R0P.MaskSemantics, `R0P.MaskPrefix, `R0P.MaskNoHit, `R1SemanticHit, `R0P.MaskEarly, `RawTranscriptFrameBytes, `OracleProgramReplay, `GSInterpolationBudget, `FiniteFieldCompleteRootCertificate, `FiniteFieldNormalizedRootFactor, `RRRootDescent, `RRChildNormalization, `RRActualTaylorSubstitutionV3, `RRActualBivariateTaylorBridgeV8, `RRDiagonalSubstitutionExpansionV27, `RRChildSliceTaylorV4, `RRRootMultiplicityTaylorV3, `RRChildSliceMultiplicityV3, `RRActualFixedParentConvolutionV7, `RRNormalizedChildSlice, `RRActualNormalizedTransition, `RRDenseCoeffVectorV6, `RRVectorRowBridgeV12, `RRVectorRowBridgeV14, `RRFiniteCoeffScannerV9, `RRVectorRowNonzeroV5, `RRVectorActualScannerV2, `RRScannedNormalizedTransition, `RRVectorNormalizedRowsV12, `RRVectorNormalizedStateV4, `RRSubstitutionTailBound, `RRVectorNormalizedCompleteV3, `RRSubstitutionOuterDegreeBound, `RRInitialFullRowsScanFacts, `RRPrefixCollector, `RRVectorPolynomialReconstructionV9, `RRRuntimeNormalizedChildReconstruction, `RRConcreteChildModel, `RRBoundedSliceScannerV5, `RRSiblingMultiplicityMassV2, `GSRootCandidateContract, `FiniteOptionSamplerComposition, `GSDecoderTapeReindex, `M31AcceptFiber, `FSRetryOutputUniformity, `M31RetryOutputFiber, `M31RejectFiber, `M31RetryAbortFiber ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ3_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ3_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ3_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ3_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ3_AUDIT_COMPLETE declarations={count} modules={selected.size}"
