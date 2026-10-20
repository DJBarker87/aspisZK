import Lean
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
import GSFinalMessageCandidateFilter
import GSRuntimeFinalDistanceEncoderBridge
import GSConcreteReceivedWordPoints
import GSConcreteReceivedWordInputs
import LiteralTerminalCandidate
import LiteralTerminalListExtract
import R1PartialJointList
import R1IncrementalJointCandidates
import R1IncrementalCandidateLoop
import GSRuntimeInitialJointKeepCore
import GSConcreteInitialRuntimeJointCandidates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`M31RejectFiber, `M31RetryAbortFiber, `M31RetryMassNatCard, `M31RetryFiberNatCardBridge, `M31EightLimbProductCount, `M31RetryFiberUniformNat, `M31RetryOutputMassNat, `M31EightLimbSuccessCount, `M31RetryMassRational, `M31EightLimbOutputLaw, `M31EquivUniformTransport, `M31WideExactPacking, `M31EightLimbAbortBound, `M31ActualEightWideSampler, `M31ActualWideSamplerTapeLaw, `M31PairedWideSamplerLaw, `M31PairedSamplerMass, `M31PairedSamplerRejectBound, `GSConcreteByteDecoderBank, `GSFinalMessageCandidateFilter, `GSRuntimeFinalDistanceEncoderBridge, `GSConcreteReceivedWordPoints, `GSConcreteReceivedWordInputs, `LiteralTerminalCandidate, `LiteralTerminalListExtract, `R1PartialJointList, `R1IncrementalJointCandidates, `R1IncrementalCandidateLoop, `GSRuntimeInitialJointKeepCore, `GSConcreteInitialRuntimeJointCandidates]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
