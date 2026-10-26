import Lean
import CurrentClaimKappaPolynomial
import CurrentClaimScalarReads
import CurrentClaimHelperCanonical
import EbyKPushExplicitTypesV1
import AspisR1EbyKPushExplicitOpsV1
import AspisR1EbyKCheckedQAllParamV1
import EbyKCheckedQConcreteAll
import EbyKCheckedQCanonicality
import AspisR1EbyKPushWideToQ
import AspisR1EbyKPushSourceConversionV1
import AspisR1EbyKPushConcreteCheckedQV1
import EbyKPushCheckedScalarCanonical
import AspisR1DotPushLocal.Types
import AspisR1DotPushLocal.Funs
import EbyKDotPushNatStep
import CheckedWrappingScalarAgreement
import EbyKDotPushCanonicalFoldBridgeV1
import EbyKDotPushActualFoldV2
import DotPushWordSource
import DotPushFourCoordinates
import DotPushSourceResidues
import DotPushSuccessResidues
import EbyKPushDotBackend
import AspisR1EbyKFinish.Types
import SelectorArrayMapRuntimeSlice
import AspisR1EbyKFinish.Funs
import AspisR1CanonicalDotFinish.Types
import AspisR1CanonicalDotFinish.Funs
import CanonicalDotReduceSemantics
import SelectorArrayMapSuccess
import CanonicalDotFinishSemantics
import EbyKFinishABI
import EbyKFinishTotal
import CurrentEbyFinishCanonical
import FinishDotSourceABI
import FinishCandidateDotTrace
import FinishCandidateDotLoopTrace
import FinishCandidateDotSuccess
import FinishAcceptedRhsCanonical
import AspisR1Stage2Accumulate.Types
import AspisR1Stage2Accumulate.Funs
import EbyKNewCutProof
import EbyKNewToPushStateABI
import FinishDotConcreteOps
import ClaimDotConcreteAdapterV1
import AspisR1S5ClaimScalarFinishCanonical
import CurrentClaimConcreteOuter
import CurrentClaimPowerReads
import FinishDotLoopCount
import FinishDotCountBoundV3
import AspisR1CanonicalQRawUnified.Types
import AspisR1CanonicalQRawUnified.Funs
import S5QRaw.SuccessTracePropV4
import S5QRaw.NoWrapFactsV5
import S5QRaw.PartialFoldBridgeV7
import S5QRaw.TraceUVBridgeV2
import R22RawQmProductResiduesV15
import R22FastPairingRawRanges
import S5CanonicalProductRangesV1
import S5QRaw.NoWrapFromCanonicalTraceV1
import S5QRaw.ActualCoefficientsFromBoundsV2
import AspisR1EbyKDotPushSourceV1.Types
import AspisR1EbyKDotPushSourceV1.LoopAdapter
import OriginalDotPushRawLoopToLiteralV1
import S5QRaw.GeneratedDotPushConnectionV2
import EbyKPowerValueCanonicalToPushV5
import S5QRaw.EbyKPushActualRawCoefficientBoundsV10
import S5QRaw.EbyKPushDecodedProductUpdateV1
import AspisR1FinishDotDecodedProductTrace
import AspisR1FinishDotReturnedProductWords
import AspisR1FinishDotReturnedProductWordsV2
import AspisR1FinishDotReturnedDecodedValueV1
import AspisR1FinishDotReturnedDeltaDecodeV1
import AspisR1FinishDotReturnedFieldProductV1
import AspisR1S5ClaimScalarConcreteQRawTrace
import CurrentClaimAggregation
import AspisR1S5ClaimScalarEmbeddedProductSum
import CurrentClaimGammaScalarSum
import CurrentClaimSelectedScalarSource
import CurrentClaimSourceAggregation
import AspisR1GammaCaller.Types
import GammaCallerExplicitHelpers
import GammaCallerDigitsModel
import AspisR1Post25Sampler.Types
import AspisR1Post25Sampler.Funs
import ExtractedQM31SamplerIndexedCandidate
import IndexedCandidateGeneratedLoopBridgeV4
import IndexedCandidateOuterByteBridgeV13
import IndexedCandidateOuterByteOutputSuccessV5
import GammaCandidateLowQuotient
import GammaCallerRankModel
import AspisR1Post25SamplerIndexedAddSmallCandidate.Types
import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import IndexedCandidateAddSmallGeneratedOneStepV1
import IndexedCandidateAddSmallLoopCanonicalV11
import IndexedCandidateAddSmallNatModelV1
import IndexedCandidateAddSmallWrapperNatModelV3
import GammaCandidateAddSmallHelpersRefine
import R1Z.ProverCommitArrayIndex25
import IndexedCandidateDecode8RetainedBridgeV3

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `CurrentClaimKappaPolynomial, `CurrentClaimScalarReads, `CurrentClaimHelperCanonical, `EbyKPushExplicitTypesV1, `AspisR1EbyKPushExplicitOpsV1, `AspisR1EbyKCheckedQAllParamV1, `EbyKCheckedQConcreteAll, `EbyKCheckedQCanonicality, `AspisR1EbyKPushWideToQ, `AspisR1EbyKPushSourceConversionV1, `AspisR1EbyKPushConcreteCheckedQV1, `EbyKPushCheckedScalarCanonical, `AspisR1DotPushLocal.Types, `AspisR1DotPushLocal.Funs, `EbyKDotPushNatStep, `CheckedWrappingScalarAgreement, `EbyKDotPushCanonicalFoldBridgeV1, `EbyKDotPushActualFoldV2, `DotPushWordSource, `DotPushFourCoordinates, `DotPushSourceResidues, `DotPushSuccessResidues, `EbyKPushDotBackend, `AspisR1EbyKFinish.Types, `SelectorArrayMapRuntimeSlice, `AspisR1EbyKFinish.Funs, `AspisR1CanonicalDotFinish.Types, `AspisR1CanonicalDotFinish.Funs, `CanonicalDotReduceSemantics, `SelectorArrayMapSuccess, `CanonicalDotFinishSemantics, `EbyKFinishABI, `EbyKFinishTotal, `CurrentEbyFinishCanonical, `FinishDotSourceABI, `FinishCandidateDotTrace, `FinishCandidateDotLoopTrace, `FinishCandidateDotSuccess, `FinishAcceptedRhsCanonical, `AspisR1Stage2Accumulate.Types, `AspisR1Stage2Accumulate.Funs, `EbyKNewCutProof, `EbyKNewToPushStateABI, `FinishDotConcreteOps, `ClaimDotConcreteAdapterV1, `AspisR1S5ClaimScalarFinishCanonical, `CurrentClaimConcreteOuter, `CurrentClaimPowerReads, `FinishDotLoopCount, `FinishDotCountBoundV3, `AspisR1CanonicalQRawUnified.Types, `AspisR1CanonicalQRawUnified.Funs, `S5QRaw.SuccessTracePropV4, `S5QRaw.NoWrapFactsV5, `S5QRaw.PartialFoldBridgeV7, `S5QRaw.TraceUVBridgeV2, `R22RawQmProductResiduesV15, `R22FastPairingRawRanges, `S5CanonicalProductRangesV1, `S5QRaw.NoWrapFromCanonicalTraceV1, `S5QRaw.ActualCoefficientsFromBoundsV2, `AspisR1EbyKDotPushSourceV1.Types, `AspisR1EbyKDotPushSourceV1.LoopAdapter, `OriginalDotPushRawLoopToLiteralV1, `S5QRaw.GeneratedDotPushConnectionV2, `EbyKPowerValueCanonicalToPushV5, `S5QRaw.EbyKPushActualRawCoefficientBoundsV10, `S5QRaw.EbyKPushDecodedProductUpdateV1, `AspisR1FinishDotDecodedProductTrace, `AspisR1FinishDotReturnedProductWords, `AspisR1FinishDotReturnedProductWordsV2, `AspisR1FinishDotReturnedDecodedValueV1, `AspisR1FinishDotReturnedDeltaDecodeV1, `AspisR1FinishDotReturnedFieldProductV1, `AspisR1S5ClaimScalarConcreteQRawTrace, `CurrentClaimAggregation, `AspisR1S5ClaimScalarEmbeddedProductSum, `CurrentClaimGammaScalarSum, `CurrentClaimSelectedScalarSource, `CurrentClaimSourceAggregation, `AspisR1GammaCaller.Types, `GammaCallerExplicitHelpers, `GammaCallerDigitsModel, `AspisR1Post25Sampler.Types, `AspisR1Post25Sampler.Funs, `ExtractedQM31SamplerIndexedCandidate, `IndexedCandidateGeneratedLoopBridgeV4, `IndexedCandidateOuterByteBridgeV13, `IndexedCandidateOuterByteOutputSuccessV5, `GammaCandidateLowQuotient, `GammaCallerRankModel, `AspisR1Post25SamplerIndexedAddSmallCandidate.Types, `AspisR1Post25SamplerIndexedAddSmallCandidate.Funs, `IndexedCandidateAddSmallGeneratedOneStepV1, `IndexedCandidateAddSmallLoopCanonicalV11, `IndexedCandidateAddSmallNatModelV1, `IndexedCandidateAddSmallWrapperNatModelV3, `GammaCandidateAddSmallHelpersRefine, `R1Z.ProverCommitArrayIndex25, `IndexedCandidateDecode8RetainedBridgeV3 ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"
