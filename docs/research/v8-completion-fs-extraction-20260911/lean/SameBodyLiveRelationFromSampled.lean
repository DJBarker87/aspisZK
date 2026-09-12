import SameBodyLiveRelationObservation
import SameBodyOODData

/-!
# Construct the live relation input from sampled OOD data

`SameBodyLiveRelationObservation.build` historically accepted a `Data` value
as an independent argument.  This wrapper executes the fail-closed
`fromSampled` constructor first and passes only its returned value to `build`.
Thus success constructs the same-body OOD provenance equality; it is not a
coherence certificate supplied by the caller.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000

namespace AspisV8Completion.SameBodyLiveRelationFromSampled

open SameBodyLiveRelationObservation SameBodyOODData
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix
open FSOracleExecution FSBoundedTranscript
open AspisV8.CanonicalRelationInput
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

inductive Error where
  | sampledData
  | relation (error : SameBodyLiveRelationObservation.Error)
  deriving DecidableEq

/-- Total executable composition.  OOD parsing/interpolation/inversion failure
and later relation-input construction failure remain distinct rejections. -/
def buildFromSampled (view : RawHashInput -> Digest208)
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
    Except Error (Ready view) :=
  match sampled : fromSampled out gamma body with
  | none => .error .sampledData
  | some data =>
      match builtEq : build view functional increment out gamma body
          middleStartDigest tape middleOracle middle middleFinalDigest middleRun
          laterOracle later laterFinalDigest laterRun data with
      | .error error => .error (.relation error)
      | .ok ready => .ok ready

/-- Success exposes the exact executable OOD-data provenance that the older
`Ready` interface omitted. -/
theorem buildFromSampled_success_sourceData
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
        laterOracle).1 = some (.ok later, laterFinalDigest))
    (ready : Ready view)
    (success : buildFromSampled view functional increment out gamma body
      middleStartDigest tape middleOracle middle middleFinalDigest middleRun
      laterOracle later laterFinalDigest laterRun = .ok ready) :
    fromSampled ready.out ready.gamma ready.body = some ready.data := by
  unfold buildFromSampled at success
  split at success
  · contradiction
  next data sampled =>
    split at success
    · contradiction
    next built builtEq =>
      have same := Except.ok.inj success
      subst ready
      have builtFields : built.out = out ∧ built.gamma = gamma ∧
          built.body = body ∧ built.data = data := by
        unfold build at builtEq
        split at builtEq
        · contradiction
        next input inputEq =>
          split at builtEq
          · contradiction
          next prepared preparedEq =>
            split at builtEq
            · have sameBuilt := Except.ok.inj builtEq
              subst built
              exact ⟨rfl, rfl, rfl, rfl⟩
            · contradiction
      simpa [builtFields.1, builtFields.2.1, builtFields.2.2.1,
        builtFields.2.2.2] using sampled

theorem buildFromSampled_success_checked
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
        laterOracle).1 = some (.ok later, laterFinalDigest))
    (ready : Ready view)
    (success : buildFromSampled view functional increment out gamma body
      middleStartDigest tape middleOracle middle middleFinalDigest middleRun
      laterOracle later laterFinalDigest laterRun = .ok ready) :
    ready.data.Checked := by
  exact fromSampled_checked ready.out ready.gamma ready.body ready.data
    (buildFromSampled_success_sourceData view functional increment out gamma body
      middleStartDigest tape middleOracle middle middleFinalDigest middleRun
      laterOracle later laterFinalDigest laterRun ready success)

#print axioms buildFromSampled_success_sourceData
#print axioms buildFromSampled_success_checked

end
end AspisV8Completion.SameBodyLiveRelationFromSampled
