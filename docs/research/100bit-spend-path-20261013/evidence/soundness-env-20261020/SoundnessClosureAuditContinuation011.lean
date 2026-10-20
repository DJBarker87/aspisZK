import Lean
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
import RRInitialFullRowsScanFacts
import RRInitialNonzeroRowBridge
import RRInitialDroppedModelBridge
import RRPrefixCollector
import RRConcreteInitialNormalizationFromFacts
import RRVectorPolynomialReconstructionV9
import RRRuntimeNormalizedChildReconstruction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`RRActualBivariateTaylorBridgeV8, `RRDiagonalSubstitutionExpansionV27, `RRChildSliceTaylorV4, `RRRootMultiplicityTaylorV3, `RRChildSliceMultiplicityV3, `RRActualFixedParentConvolutionV7, `RRNormalizedChildSlice, `RRActualNormalizedTransition, `RRDenseCoeffVectorV6, `RRVectorRowBridgeV12, `RRVectorRowBridgeV14, `RRFiniteCoeffScannerV9, `RRVectorRowNonzeroV5, `RRVectorActualScannerV2, `RRScannedNormalizedTransition, `RRVectorNormalizedRowsV12, `RRVectorNormalizedStateV4, `RRSubstitutionTailBound, `RRVectorNormalizedCompleteV3, `RRFiniteRootSamplerNormalizedStateBridge, `RRSubstitutionOuterDegreeBound, `RRConcreteState, `RRConcreteStatePolynomialView, `RRInitialFullRowsScanFacts, `RRInitialNonzeroRowBridge, `RRInitialDroppedModelBridge, `RRPrefixCollector, `RRConcreteInitialNormalizationFromFacts, `RRVectorPolynomialReconstructionV9, `RRRuntimeNormalizedChildReconstruction]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
