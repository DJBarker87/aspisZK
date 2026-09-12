import SameBodyReplayableRunFromSampledIntegration
import FSV7PrefixBridge

/-!
# Replayable source integration at the constructed old view

The preceding replayable execution determines its final oracle state.  This
leaf specializes the sampled-relation classification to the actual
`oldView` induced by that returned state, eliminating the arbitrary hash-view
parameter without adding a view-equality premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.SameBodyReplayableOldViewIntegration

open SameBodyReplayableRunFromSampledIntegration
open ExtractionCollectorReplayableSource
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix
open FSV8PostOODGammaScript
open FSOracleExecution FSBoundedTranscript
open AspisV8.CanonicalRelationInput
open AspisV8.OODInterpolant
open AspisPool.V7MerkleQueryGrammar
open AspisK1.V7FsStateRestorationCoupling
open AspisV8Completion.FSV7PrefixBridge

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev Point := FSV7OODBodyScript.Point
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

noncomputable section

def successful_replayable_run_at_oldView
    {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (record : Record) (finalDigest : Block)
    (success :
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).1 = some (.ok record, finalDigest)) :=
  @successful_replayable_run_classifies_sampled_relation
    (fun input => oldView
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).2 input)
    n m
    firstWork secondWork producer increment body digest tape oracle record finalDigest
    success

#print axioms successful_replayable_run_at_oldView

end
end AspisV8Completion.SameBodyReplayableOldViewIntegration
