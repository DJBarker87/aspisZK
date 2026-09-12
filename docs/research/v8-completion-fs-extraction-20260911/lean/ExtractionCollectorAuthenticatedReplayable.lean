import ExtractionCollectorReplayableSource
import FSV7SelectedBodyScript
import SameBodyLivePreparedIncrement

/-!
# Replayable source followed by its same-body authenticated openings

The live source produces the q22 list before this continuation is selected.
Only a list carrying the sampler's actual validity and length facts is turned
into a typed schedule.  The selected leaf/node verifier then consumes the
same returned body and the roots fixed at the earlier chronological cuts.

This is still a functional hash-script endpoint.  It does not execute the
relation terminal, construct a payment witness, or refine the pinned Rust
mutable implementation.  In particular, a successful transcript prefix is
not called complete verifier acceptance here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.ExtractionCollectorAuthenticatedReplayable

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSExposureOrder FSFirstFresh FSQuerySchedule
open ExtractionCollectorReplayableSource
open FSLiveSelectedMiddleQueryRho
open SameBodyLivePreparedIncrement
open FSV7PrefixBridge FSV7SelectedBodyScript
open FSAuthenticationPrefixes
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev RootCuts := FSBoundedTranscript.RootCuts
abbrev Position := AspisPool.V7MerkleQueryExtractor.Position
abbrev Point := ExtractionCollectorReplayableSource.Point
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

noncomputable section

inductive Error where
  | source (error : ExtractionCollectorReplayableSource.Error)
  | invalidSchedule
  deriving DecidableEq

structure Authenticated where
  record : ExtractionCollectorReplayableSource.Record
  trace : OrderedRawQueryLog

abbrev Returned := Except Error Authenticated × Block

/-- The selected schedule has a fixed 836-call allowance: 792 node levels
plus two leaf calls for each of the 22 ordinals. -/
theorem bodyAllowance_eq
    (positions : Fin 22 -> Position) : bodyAllowance positions = 836 := by
  unfold bodyAllowance
  have permutation := sorted_ordinals_perm positions
  have length : (sortedOrdinals positions).length = 22 := by
    rw [permutation.length_eq]
    simp
  omega

/-- Cast only the static allowance.  No dummy hash call is performed. -/
def selected22 (cuts : RootCuts) (positions : Fin 22 -> Position)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) :
    Script (List UInt8) Block OrderedRawQueryLog 836 :=
  Eq.mp (congrArg (Script (List UInt8) Block OrderedRawQueryLog)
    (bodyAllowance_eq positions)) (selectedScript cuts positions body)

theorem run_cast_allowance {A : Type} {n m : Nat} (equal : n = m)
    (program : Script (List UInt8) Block A n) (tape : Tape)
    (oracle : FSBoundedTranscript.Oracle) :
    run tape
      (Eq.mp (congrArg (Script (List UInt8) Block A) equal) program) oracle =
      run tape program oracle := by
  cases equal
  rfl

theorem run_selected22 (tape : Tape) (cuts : RootCuts)
    (positions : Fin 22 -> Position)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte)
    (oracle : FSBoundedTranscript.Oracle) :
    run tape (selected22 cuts positions body) oracle =
      run tape (selectedScript cuts positions body) oracle := by
  exact run_cast_allowance (bodyAllowance_eq positions)
    (selectedScript cuts positions body) tape oracle

/-- Execute authentication only after the source has really returned a record
and its live sampler result supplies a valid typed q22 schedule. -/
noncomputable def authenticatedScript {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (cuts : RootCuts) (body : Bytes) (digest : Block) := by
  classical
  exact FSTranscriptScript.bind (m := 836)
      (replayableScript firstWork secondWork producer increment body digest)
      fun (returned : ExtractionCollectorReplayableSource.Returned) =>
    match returned.1 with
    | .error e => .done (Except.error (Error.source e), returned.2)
    | .ok record =>
      if h : ValidAccepted record.middle.queries /\
          record.middle.queries.length = 22 then
        FSTranscriptScript.bind (m := 0) (selected22 cuts
            (liveSchedule record.middle h.1 h.2).positions (encode record.body))
          fun trace => .done
            (Except.ok (Authenticated.mk record trace), returned.2)
      else .done (Except.error Error.invalidSchedule, returned.2)

/-- A successful combined run decomposes into the exact source result and a
successful same-body Merkle run on its constructed live schedule. -/
theorem successful_authenticated_components {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (cuts : RootCuts) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : FSBoundedTranscript.Oracle)
    (authenticated : Authenticated)
    (finalDigest : Block)
    (success :
      (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body digest) oracle).1 = some (.ok authenticated, finalDigest)) :
    exists sourceDigest valid count,
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).1 = some (.ok authenticated.record, sourceDigest) /\
      (run tape (selectedScript cuts
          (liveSchedule authenticated.record.middle valid count).positions
          (encode authenticated.record.body))
        (run tape (replayableScript firstWork secondWork producer increment body digest)
          oracle).2).1 = some authenticated.trace /\
      authenticated.record.body = body /\ finalDigest = sourceDigest := by
  unfold authenticatedScript at success
  rw [run_bind] at success
  cases sourceRun :
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).1 with
  | none => simp [sourceRun] at success
  | some returned =>
    rcases returned with ⟨sourceResult, sourceDigest⟩
    cases sourceResult with
    | error e => simp [sourceRun, run] at success
    | ok record =>
      simp only [sourceRun] at success
      split at success
      next h =>
        rw [run_bind, run_selected22] at success
        cases merkleRun :
            (run tape (selectedScript cuts
              (liveSchedule record.middle h.1 h.2).positions (encode record.body))
              (run tape
                (replayableScript firstWork secondWork producer increment body digest)
                oracle).2).1 with
        | none => simp [merkleRun] at success
        | some trace =>
          simp [merkleRun, run] at success
          rcases success with ⟨⟨rfl, rfl⟩, rfl⟩
          have bodySame : record.body = body := by
            obtain ⟨_, _, _, _, _, _, _, _, _, exactRecord⟩ :=
              successful_run_components firstWork secondWork producer increment
                body digest tape oracle record sourceDigest sourceRun
            simpa [exactRecord]
          exact ⟨sourceDigest, h.1, h.2, by simpa using sourceRun, merkleRun,
            bodySame, rfl⟩
      next h => simp [run] at success

/-- Functional authentication is constructed from the combined run; neither
the Merkle success object nor the opening-call inclusion is supplied. -/
theorem successful_constructs_merkle {n m : Nat}
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (cuts : RootCuts) (body : Bytes) (digest : Block)
    (tape : Tape) (oracle : FSBoundedTranscript.Oracle)
    (authenticated : Authenticated)
    (finalDigest : Block)
    (coherent : LogConsistent oracle)
    (success :
      (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body digest) oracle).1 = some (.ok authenticated, finalDigest)) :
    exists valid count,
      let positions :=
        (liveSchedule authenticated.record.middle valid count).positions
      ∃ merkle : SuccessfulMerkleRun
          (oldView (run tape (authenticatedScript firstWork secondWork producer
            increment cuts body digest) oracle).2)
          positions (encode authenticated.record.body),
        merkle.trace = authenticated.trace /\
        merkle.wire.roots 0 = root208 cuts.c1 /\
        merkle.wire.roots 1 = root208 cuts.c2 /\
        TraceIncludedInLog
          (leafLog positions (wireRecords merkle.wire) ++ merkle.trace)
          (oldLog (run tape (authenticatedScript firstWork secondWork producer
            increment cuts body digest) oracle).2) := by
  obtain ⟨sourceDigest, valid, count, sourceRun, merkleRun, bodySame, _⟩ :=
    successful_authenticated_components firstWork secondWork producer increment
      cuts body digest tape oracle authenticated finalDigest success
  have afterSource : LogConsistent
      (run tape (replayableScript firstWork secondWork producer increment body digest)
        oracle).2 := run_log_consistent tape _ _ coherent
  have finalOracle :
      (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body digest) oracle).2 =
      (run tape (selectedScript cuts
        (liveSchedule authenticated.record.middle valid count).positions
        (encode authenticated.record.body))
        (run tape (replayableScript firstWork secondWork producer increment body digest)
          oracle).2).2 := by
    unfold authenticatedScript
    rw [run_bind, sourceRun]
    simp only
    rw [dif_pos (show ValidAccepted authenticated.record.middle.queries /\
      authenticated.record.middle.queries.length = 22 from ⟨valid, count⟩)]
    rw [run_bind, run_selected22, merkleRun]
    rfl
  rw [finalOracle]
  have constructed := selected_constructs tape cuts
    (liveSchedule authenticated.record.middle valid count).positions
    (encode authenticated.record.body)
    (run tape (replayableScript firstWork secondWork producer increment body digest)
      oracle).2 authenticated.trace afterSource merkleRun
  rcases constructed with ⟨merkle, traceEq, root0, root1, included⟩
  exact ⟨valid, count, merkle, traceEq, root0, root1, included⟩

#print axioms bodyAllowance_eq
#print axioms run_selected22
#print axioms successful_authenticated_components
#print axioms successful_constructs_merkle

end
end AspisV8Completion.ExtractionCollectorAuthenticatedReplayable
