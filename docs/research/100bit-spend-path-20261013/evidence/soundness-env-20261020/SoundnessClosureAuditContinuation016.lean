import Lean
import LiteralWordAgreement
import R13MultiproofReadSet
import R13PaddedLeafPrograms
import R22BatchedPushTotal
import R22BatchedValueTotal
import R22CanonicalM31AddSub
import R22CurrentReducerMul
import R22CanonicalCM31
import R22CanonicalQM31
import R22ControlBounds
import R22DecodeValueTotal
import R22DecodeLoopTotal
import R22FastPairingPrimitiveBounds
import R22FastPairingRawRanges
import R22OverflowAudit
import RawAdaptiveClassifierStartBound
import RawPublicSelectionLift
import RawLiteralDecoderCompletion
import RawFullPublicSelection
import RawLiteralDecoderRestore
import RawLiteralRecordedDecoder
import RawFullPublicRun
import RawCompiledTranscript
import RawLiteralCompiledDecoder
import RawCompiledDecoderCompletion
import RawAdaptiveCompiledCompletion
import RawCutCompilerLaw
import RawAdaptiveDecoderInjection
import RawAdaptiveMembershipBound
import RawChecksConstructorScheduleV4

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`LiteralWordAgreement, `R13MultiproofReadSet, `R13PaddedLeafPrograms, `R22BatchedPushTotal, `R22BatchedValueTotal, `R22CanonicalM31AddSub, `R22CurrentReducerMul, `R22CanonicalCM31, `R22CanonicalQM31, `R22ControlBounds, `R22DecodeValueTotal, `R22DecodeLoopTotal, `R22FastPairingPrimitiveBounds, `R22FastPairingRawRanges, `R22OverflowAudit, `RawAdaptiveClassifierStartBound, `RawPublicSelectionLift, `RawLiteralDecoderCompletion, `RawFullPublicSelection, `RawLiteralDecoderRestore, `RawLiteralRecordedDecoder, `RawFullPublicRun, `RawCompiledTranscript, `RawLiteralCompiledDecoder, `RawCompiledDecoderCompletion, `RawAdaptiveCompiledCompletion, `RawCutCompilerLaw, `RawAdaptiveDecoderInjection, `RawAdaptiveMembershipBound, `RawChecksConstructorScheduleV4]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
