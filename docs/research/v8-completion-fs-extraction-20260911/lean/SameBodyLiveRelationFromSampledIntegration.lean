import SameBodyLiveRelationFromSampled

/-!
# Chronological integration of sampled OOD data

This leaf classifies the existing successful middle/later execution inputs by
the executable `buildFromSampled` constructor.  The success branch exposes
the exact `fromSampled` provenance and `Checked` proof; parser, inverse, and
relation-input failures remain explicit named errors.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000

namespace AspisV8Completion.SameBodyLiveRelationFromSampledIntegration

open SameBodyLiveRelationFromSampled
open SameBodyLiveRelationObservation
open SameBodyOODData
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix
open FSOracleExecution FSBoundedTranscript
open AspisV8.CanonicalRelationInput
open AspisV8.OODInterpolant
open AspisPool.V7MerkleQueryGrammar

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev K := SameBodyLiveRelationObservation.K
abbrev OODResult := SameBodyLiveRelationObservation.OODResult
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

noncomputable section

theorem buildFromSampled_success_or_named_rejection
    (view : RawHashInput -> Digest208)
    (functional : FunctionalProducer) (increment : IncrementProducer)
    (out : OODResult) (gamma : K) (body : Bytes)
    (middleStartDigest : Block) (tape : Tape) (middleOracle : Oracle)
    (middle : FSLiveSelectedMiddleQueryRho.Success) (middleFinalDigest : Block)
    (middleRun :
      (run tape (middleQueryRhoScript functional out gamma body middleStartDigest)
        middleOracle).1 = some (.ok middle, middleFinalDigest))
    (laterOracle : Oracle) (later : FSLiveLaterRelationSuffix.Success)
    (laterFinalDigest : Block)
    (laterRun :
      (run tape (laterScript increment out gamma middle body middleFinalDigest)
        laterOracle).1 = some (.ok later, laterFinalDigest)) :
    (∃ ready : Ready view,
        buildFromSampled view functional increment out gamma body
            middleStartDigest tape middleOracle middle middleFinalDigest middleRun
            laterOracle later laterFinalDigest laterRun = .ok ready ∧
        fromSampled ready.out ready.gamma ready.body = some ready.data ∧
        ready.data.Checked) ∨
      (∃ error : SameBodyLiveRelationFromSampled.Error,
        buildFromSampled view functional increment out gamma body
            middleStartDigest tape middleOracle middle middleFinalDigest middleRun
            laterOracle later laterFinalDigest laterRun = .error error) := by
  cases resultEq : buildFromSampled view functional increment out gamma body
      middleStartDigest tape middleOracle middle middleFinalDigest middleRun
      laterOracle later laterFinalDigest laterRun with
  | error error =>
      exact Or.inr ⟨error, rfl⟩
  | ok ready =>
      have h : buildFromSampled view functional increment out gamma body
          middleStartDigest tape middleOracle middle middleFinalDigest middleRun
          laterOracle later laterFinalDigest laterRun = .ok ready := resultEq
      exact Or.inl ⟨ready, rfl,
        buildFromSampled_success_sourceData view functional increment out gamma body
          middleStartDigest tape middleOracle middle middleFinalDigest middleRun
          laterOracle later laterFinalDigest laterRun ready h,
        buildFromSampled_success_checked view functional increment out gamma body
          middleStartDigest tape middleOracle middle middleFinalDigest middleRun
          laterOracle later laterFinalDigest laterRun ready h⟩

#print axioms buildFromSampled_success_or_named_rejection

end
end AspisV8Completion.SameBodyLiveRelationFromSampledIntegration
