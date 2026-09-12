import SameBodyLiveTerminalInput
import SameBodyLivePreparedIncrement

/-!
# One live relation observation with an authenticated increment

This leaf joins the chronological middle and later suffixes to the functional
opening pipeline.  Construction fails unless the bytes actually absorbed by
the later suffix are exactly the canonical encoding of the shifted scalar
computed from the same body's authenticated q22 openings.

The OOD `Data`, hash view, ordinary scalar and causal relation strategy remain
later source/refinement boundaries.  No terminal acceptance, payment witness,
freshness or probability claim is made here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.SameBodyLiveRelationObservation

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveSelectedMiddleQueryRho FSLiveLaterRelationSuffix
open SameBodyLiveTerminalInput SameBodyLivePreparedIncrement
open SameBodyAuthenticatedIncrement
open AspisPool.V7MerkleQueryGrammar
open AspisV8.OODInterpolant

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev Oracle := FSBoundedTranscript.Oracle
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

inductive Error where
  | canonicalBody
  | openedPipeline
  | incrementMismatch
  deriving DecidableEq

/-- Every field is returned by an executed constructor.  In particular,
`incrementBytes` is not an equality proof supplied to a terminal theorem. -/
structure Ready (view : RawHashInput -> Digest208) where
  functional : FunctionalProducer
  increment : IncrementProducer
  out : OODResult
  gamma : K
  body : Bytes
  middleStartDigest : Block
  tape : Tape
  middleOracle : Oracle
  middle : FSLiveSelectedMiddleQueryRho.Success
  middleFinalDigest : Block
  middleRun :
    (run tape (middleQueryRhoScript functional out gamma body middleStartDigest)
      middleOracle).1 = some (.ok middle, middleFinalDigest)
  laterOracle : Oracle
  later : FSLiveLaterRelationSuffix.Success
  laterFinalDigest : Block
  laterRun :
    (run tape (laterScript increment out gamma middle body middleFinalDigest)
      laterOracle).1 = some (.ok later, laterFinalDigest)
  data : Data (K := K)
  input : SameBodyLiveTerminalInput.Input
  inputRun : SameBodyLiveTerminalInput.fromBody increment out gamma middle later body =
    some input
  prepared : SameBodyAuthenticatedIncrement.Prepared view
  preparedRun : prepareFromRun view functional out gamma body middleStartDigest tape
    middleOracle middle middleFinalDigest middleRun data = .ok prepared
  incrementBytes : input.incrementBytes = prepared.bytes

/-- Build the exact input used by a later relation check.  `middleRun` is the
actual chronological query/rho suffix success used to construct the schedule;
`laterRun` records that the supplied later result came from the script which
absorbed `increment.bytes`. -/
def build (view : RawHashInput -> Digest208)
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
    (data : Data (K := K)) : Except Error (Ready view) :=
  match inputEq : SameBodyLiveTerminalInput.fromBody increment out gamma middle
      later body with
  | none => .error .canonicalBody
  | some input =>
      match preparedEq : prepareFromRun view functional out gamma body
          middleStartDigest tape middleOracle middle middleFinalDigest middleRun data with
      | .error _ => .error .openedPipeline
      | .ok prepared =>
          if bytesEq : input.incrementBytes = prepared.bytes then
            .ok ⟨functional, increment, out, gamma, body, middleStartDigest,
              tape, middleOracle, middle, middleFinalDigest, middleRun,
              laterOracle, later, laterFinalDigest, laterRun, data,
              input, inputEq, prepared, preparedEq, bytesEq⟩
          else .error .incrementMismatch

theorem build_success (view : RawHashInput -> Digest208)
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
    (data : Data (K := K)) (ready : Ready view)
    (success : build view functional increment out gamma body middleStartDigest tape
      middleOracle middle middleFinalDigest middleRun laterOracle later
      laterFinalDigest laterRun data = .ok ready) :
    ready.input.body = body /\
    ready.input.ood = out /\
    ready.input.gamma = gamma /\
    ready.input.middle = middle /\
    ready.input.later = later /\
    ready.prepared.body = body /\
    ready.prepared.query =
      (liveScheduleFromRun functional out gamma body middleStartDigest tape
        middleOracle middle middleFinalDigest middleRun).positions /\
    ready.prepared.alpha = middle.alpha0 /\
    ready.prepared.rho = middle.rho /\
    ready.input.incrementBytes = ready.prepared.bytes := by
  unfold build at success
  split at success
  · contradiction
  next input inputEq =>
    split at success
    · contradiction
    next prepared preparedEq =>
      split at success
      · rename_i bytesEq
        have same := Except.ok.inj success
        subst ready
        have inputFacts := SameBodyLiveTerminalInput.fromBody_constructs_canonical
          increment out gamma middle later body input inputEq
        have preparedFacts := prepareFromRun_success view functional out gamma body
          middleStartDigest tape middleOracle middle middleFinalDigest middleRun data
          prepared preparedEq
        have preparedBody : prepared.body = body := by
          unfold prepareFromRun SameBodyAuthenticatedIncrement.prepare at preparedEq
          split at preparedEq
          · contradiction
          · cases preparedEq
            rfl
        exact ⟨inputFacts.1, inputFacts.2.2.1, inputFacts.2.2.2.1,
          inputFacts.2.2.2.2.1, inputFacts.2.2.2.2.2.1,
          preparedBody, preparedFacts.1, preparedFacts.2.1, preparedFacts.2.2, bytesEq⟩
      · contradiction

/-- The scalar fed to `SameBodyRelation.consume` is the one whose canonical
bytes the chronological later script absorbed. -/
theorem absorbed_increment_is_relation_increment
    {view : RawHashInput -> Digest208} (ready : Ready view) :
    (run ready.tape
      (laterScript ready.increment ready.out ready.gamma ready.middle ready.body
        ready.middleFinalDigest) ready.laterOracle).1 =
        some (.ok ready.later, ready.laterFinalDigest) /\
    ready.input.incrementBytes = ready.prepared.bytes /\
    ready.prepared.relationIncrement ready.input.final256 ready.prepared.query
        ready.prepared.rho = ready.prepared.scalar := by
  exact ⟨ready.laterRun, ready.incrementBytes,
    relation_increment_exact ready.prepared _⟩

#print axioms build_success
#print axioms absorbed_increment_is_relation_increment

end
end AspisV8Completion.SameBodyLiveRelationObservation
