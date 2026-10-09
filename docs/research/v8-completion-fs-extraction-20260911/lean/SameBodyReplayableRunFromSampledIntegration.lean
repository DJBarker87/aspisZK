import ExtractionCollectorReplayableSource
import SameBodyLiveRelationFromSampledIntegration

/-!
# Replayable source run into sampled relation construction

This is the chronological adapter from the actual replayable source run to
the sampled OOD-data relation constructor.  The preceding run is decomposed
at its real source, middle, and later boundaries; `buildFromSampled` then
classifies the continuation as a `Ready` result with executable provenance or
as a named parser/inverse/relation rejection.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.SameBodyReplayableRunFromSampledIntegration

open ExtractionCollectorReplayableSource
open SameBodyLiveRelationFromSampledIntegration
open SameBodyLiveRelationFromSampled
open SameBodyLiveRelationObservation
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix
open FSV8PostOODGammaScript
open FSOracleExecution FSBoundedTranscript
open AspisV8.CanonicalRelationInput
open AspisV8.OODInterpolant
open AspisPool.V7MerkleQueryGrammar

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV7OODBodyScript.Point
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

noncomputable section

theorem successful_replayable_run_classifies_sampled_relation
    {view : RawHashInput -> Digest208}
    {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (record : Record) (finalDigest : Block)
    (success :
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).1 = some (.ok record, finalDigest)) :
    ∃ out gamma prefixDigest middle middleDigest later,
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).1 =
          some (.ok (out, gamma), prefixDigest) ∧
      (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
        (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2).1 =
          some (.ok middle, middleDigest) ∧
      (run tape (laterScript increment out gamma middle body middleDigest)
        (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
          (run tape (sourceThenGammaScript firstWork secondWork body digest)
            oracle).2).2).1 = some (.ok later, finalDigest) ∧
      (record = Record.mk body out gamma middle later) ∧
      (∀ (middleRun :
          (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
            (run tape (sourceThenGammaScript firstWork secondWork body digest)
              oracle).2).1 = some (.ok middle, middleDigest))
        (laterRun :
          (run tape (laterScript increment out gamma middle body middleDigest)
            (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
              (run tape (sourceThenGammaScript firstWork secondWork body digest)
                oracle).2).2).1 = some (.ok later, finalDigest)),
        ((∃ ready : Ready view,
        buildFromSampled view producer increment out gamma body prefixDigest tape
            (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2
            middle middleDigest middleRun
            (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
              (run tape (sourceThenGammaScript firstWork secondWork body digest)
                oracle).2).2
            later finalDigest laterRun = .ok ready ∧
          SameBodyOODData.fromSampled ready.out ready.gamma ready.body = some ready.data ∧
          ready.data.Checked) ∨
        (∃ error : SameBodyLiveRelationFromSampled.Error,
          buildFromSampled view producer increment out gamma body prefixDigest tape
            (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2
            middle middleDigest middleRun
            (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
              (run tape (sourceThenGammaScript firstWork secondWork body digest)
                oracle).2).2
            later finalDigest laterRun = .error error))) := by
  rcases successful_run_components firstWork secondWork producer increment body digest
      tape oracle record finalDigest success with
    ⟨out, gamma, prefixDigest, middle, middleDigest, later,
      prefixRun, middleRun0, laterRun0, recordEq⟩
  let middleOracle :=
    (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2
  let laterOracle :=
    (run tape (middleQueryRhoScript producer out gamma body prefixDigest)
      (run tape (sourceThenGammaScript firstWork secondWork body digest) oracle).2).2
  refine ⟨out, gamma, prefixDigest, middle, middleDigest, later,
    prefixRun, middleRun0, laterRun0, recordEq, ?_⟩
  intro middleRun laterRun
  have classified := buildFromSampled_success_or_named_rejection
    view producer increment out gamma body prefixDigest tape middleOracle middle
    middleDigest middleRun laterOracle later finalDigest laterRun
  simpa [middleOracle, laterOracle] using classified

#print axioms successful_replayable_run_classifies_sampled_relation

end
end AspisV8Completion.SameBodyReplayableRunFromSampledIntegration
