import Lean
import GSInterpolationBudget
import GSInterpolationBackendWitness
import GSRawStateCoefficientBridgeV6
import GSRawStateConstructorContractV1
import GSConcreteInterpolation
import RRFixedTapeRecovery
import GSConcreteRootRecoveryDefinitions
import GSConcreteRootRecoveryEquations
import GSRootCandidateContract
import GSConcreteRootRecovery
import GSFixedInputDecoderFamily
import WideExactInitialInverseComputableV2
import WideExactInitialParityCBridgeV9
import WideExactInitialMessageComputableV1
import WideExactInitialMessageComputableV4
import WideExactInitialInverseV5
import WideExactInitialInverseBridgeV2
import WideExactInitialCirclePairInverseV5
import InitialMessageComputableV8
import InitialMessageForwardFilterV3
import InitialMessagePublicFilter
import GSInitialMessageCandidateFilter
import GSRuntimeInitialDistanceEncoderBridge
import GSInterpolationAgreementCore
import GSInitialActualMessageRecovery
import GSActualRuntimeCloseCompleteness
import GSDecoderTapeReindex
import GSRejectingSamplerDecoderBank
import M31AcceptFiber
import M31RetryOutputFiber

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`GSInterpolationBudget, `GSInterpolationBackendWitness, `GSRawStateCoefficientBridgeV6, `GSRawStateConstructorContractV1, `GSConcreteInterpolation, `RRFixedTapeRecovery, `GSConcreteRootRecoveryDefinitions, `GSConcreteRootRecoveryEquations, `GSRootCandidateContract, `GSConcreteRootRecovery, `GSFixedInputDecoderFamily, `WideExactInitialInverseComputableV2, `WideExactInitialParityCBridgeV9, `WideExactInitialMessageComputableV1, `WideExactInitialMessageComputableV4, `WideExactInitialInverseV5, `WideExactInitialInverseBridgeV2, `WideExactInitialCirclePairInverseV5, `InitialMessageComputableV8, `InitialMessageForwardFilterV3, `InitialMessagePublicFilter, `GSInitialMessageCandidateFilter, `GSRuntimeInitialDistanceEncoderBridge, `GSInterpolationAgreementCore, `GSInitialActualMessageRecovery, `GSActualRuntimeCloseCompleteness, `GSDecoderTapeReindex, `GSRejectingSamplerDecoderBank, `M31AcceptFiber, `M31RetryOutputFiber]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
