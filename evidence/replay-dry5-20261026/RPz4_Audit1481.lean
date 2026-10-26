import Lean
import FiniteFieldNormalizedRootFactor
import CompPolySplitStateClosure
import CompPolyFactorAbortBound
import CompPolyCompleteRoots
import CompPolySequentialAbortBound
import CompPolySequentialRootsContract
import SequentialFiniteTapeLaw
import CompPolyFiniteRootSampler
import CompPolyGeneralRootsProgram
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
import RRFiniteRootSamplerNormalizedStateBridge
import RRSubstitutionOuterDegreeBound
import RRConcreteState
import RRConcreteStatePolynomialView
import GSRawStateCoefficientBridgeV6
import GSRawStateConstructorContractV1
import GSConcreteInterpolation
import RRInitialFullRowsScanFacts
import RRInitialNonzeroRowBridge
import RRInitialDroppedModelBridge
import RRPrefixCollector
import RRConcreteInitialNormalizationFromFacts
import RRVectorPolynomialReconstructionV9
import RRRuntimeNormalizedChildReconstruction
import RRConcreteChildModel
import RRConcreteRawStateValidity
import RRBoundedSliceScannerV5
import RRConcreteNormalizeChildTotal
import CompPolyGeneralRootIndependentLaw
import CompPolyGeneralRootQueryCost
import RRConcreteChildrenProgram
import RRConcreteValidState
import RRConcreteInitialValidStateFromFacts
import RRProgramWalkRelation
import RRProgramRecoveryContracts
import RRProgramSequentialContract
import CompPolyGeneralFiniteRootSampler
import RRSiblingMultiplicityMassV2
import RRReturnedRootMass
import RRConcreteTraversal
import RRConcreteTraversalLaw
import RRConcreteRetryBudget
import RRConcreteRawRecovery
import RRFixedTapeRecovery
import GSConcreteRootRecoveryDefinitions
import GSConcreteRootRecoveryEquations
import GSRootCandidateContract
import GSConcreteRootRecovery
import FixedInputBankUnionBound
import GSFixedInputDecoderFamily
import FiniteOptionSamplerComposition
import GSDecoderTapeReindex
import GSRejectingSamplerDecoderBank
import M31AcceptFiber
import FSRetryOutputUniformity
import M31RetryOutputFiber
import M31RejectFiber
import M31RetryAbortFiber
import M31RetryMassNatCard
import M31RetryFiberNatCardBridge
import M31EightLimbProductCount
import M31RetryFiberUniformNat
import M31RetryOutputMassNat
import M31EightLimbSuccessCount
import M31RetryMassRational
import M31EightLimbOutputLaw
import M31EquivUniformTransport
import M31WideExactPacking
import M31EightLimbAbortBound
import M31ActualEightWideSampler
import M31ActualWideSamplerTapeLaw
import M31PairedWideSamplerLaw
import M31PairedSamplerMass
import M31PairedSamplerRejectBound
import GSConcreteByteDecoderBank
import WideExactNaturalBasisComputableV16
import InitialForwardEncoderBaseV9
import CompPoly.Univariate.Lagrange
import WideExactInitialInverseComputableV2

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `FiniteFieldNormalizedRootFactor, `CompPolySplitStateClosure, `CompPolyFactorAbortBound, `CompPolyCompleteRoots, `CompPolySequentialAbortBound, `CompPolySequentialRootsContract, `SequentialFiniteTapeLaw, `CompPolyFiniteRootSampler, `CompPolyGeneralRootsProgram, `RRRootDescent, `RRChildNormalization, `RRActualTaylorSubstitutionV3, `RRActualBivariateTaylorBridgeV8, `RRDiagonalSubstitutionExpansionV27, `RRChildSliceTaylorV4, `RRRootMultiplicityTaylorV3, `RRChildSliceMultiplicityV3, `RRActualFixedParentConvolutionV7, `RRNormalizedChildSlice, `RRActualNormalizedTransition, `RRDenseCoeffVectorV6, `RRVectorRowBridgeV12, `RRVectorRowBridgeV14, `RRFiniteCoeffScannerV9, `RRVectorRowNonzeroV5, `RRVectorActualScannerV2, `RRScannedNormalizedTransition, `RRVectorNormalizedRowsV12, `RRVectorNormalizedStateV4, `RRSubstitutionTailBound, `RRVectorNormalizedCompleteV3, `RRFiniteRootSamplerNormalizedStateBridge, `RRSubstitutionOuterDegreeBound, `RRConcreteState, `RRConcreteStatePolynomialView, `GSRawStateCoefficientBridgeV6, `GSRawStateConstructorContractV1, `GSConcreteInterpolation, `RRInitialFullRowsScanFacts, `RRInitialNonzeroRowBridge, `RRInitialDroppedModelBridge, `RRPrefixCollector, `RRConcreteInitialNormalizationFromFacts, `RRVectorPolynomialReconstructionV9, `RRRuntimeNormalizedChildReconstruction, `RRConcreteChildModel, `RRConcreteRawStateValidity, `RRBoundedSliceScannerV5, `RRConcreteNormalizeChildTotal, `CompPolyGeneralRootIndependentLaw, `CompPolyGeneralRootQueryCost, `RRConcreteChildrenProgram, `RRConcreteValidState, `RRConcreteInitialValidStateFromFacts, `RRProgramWalkRelation, `RRProgramRecoveryContracts, `RRProgramSequentialContract, `CompPolyGeneralFiniteRootSampler, `RRSiblingMultiplicityMassV2, `RRReturnedRootMass, `RRConcreteTraversal, `RRConcreteTraversalLaw, `RRConcreteRetryBudget, `RRConcreteRawRecovery, `RRFixedTapeRecovery, `GSConcreteRootRecoveryDefinitions, `GSConcreteRootRecoveryEquations, `GSRootCandidateContract, `GSConcreteRootRecovery, `FixedInputBankUnionBound, `GSFixedInputDecoderFamily, `FiniteOptionSamplerComposition, `GSDecoderTapeReindex, `GSRejectingSamplerDecoderBank, `M31AcceptFiber, `FSRetryOutputUniformity, `M31RetryOutputFiber, `M31RejectFiber, `M31RetryAbortFiber, `M31RetryMassNatCard, `M31RetryFiberNatCardBridge, `M31EightLimbProductCount, `M31RetryFiberUniformNat, `M31RetryOutputMassNat, `M31EightLimbSuccessCount, `M31RetryMassRational, `M31EightLimbOutputLaw, `M31EquivUniformTransport, `M31WideExactPacking, `M31EightLimbAbortBound, `M31ActualEightWideSampler, `M31ActualWideSamplerTapeLaw, `M31PairedWideSamplerLaw, `M31PairedSamplerMass, `M31PairedSamplerRejectBound, `GSConcreteByteDecoderBank, `WideExactNaturalBasisComputableV16, `InitialForwardEncoderBaseV9, `CompPoly.Univariate.Lagrange, `WideExactInitialInverseComputableV2 ]
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
