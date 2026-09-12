import ExtractionCollectorAuthenticatedReplayable
import FSV7SourceAuthentication

/-!
# Chronological commitment prefixes through live selected openings

This leaf starts at the empty shared oracle, executes the bounded C1 and C2
builders at their actual cuts, then continues from the resulting transcript
with the replayable source and its live q22 selected-body Merkle suffix.
Successful authentication therefore constructs both prefix-answer/inclusion
facts and the leaf/node inclusion in one final log.

It does not assert that the opening arithmetic pipeline succeeds, relation
acceptance, payment acceptance, freshness, probability, or literal Rust
refinement.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.SameBodyChronologicalAuthentication

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticationPrefixes FSAuthenticationSuffix FSV7PrefixBridge
open ExtractionCollectorReplayableSource
open ExtractionCollectorAuthenticatedReplayable
open FSLiveSelectedMiddleQueryRho SameBodyLivePreparedIncrement
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.AuthenticatedEarlyC1Prefix
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun
open AspisV8.OODInterpolant
open AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.PostQueryFunctional
open AspisV8.SameBodyAuthenticatedSlots
open SameBodyAuthenticatedIncrement

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev RootCuts := FSBoundedTranscript.RootCuts
abbrev Point := FSV7OODBodyScript.Point
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer

noncomputable section

/-- One chronological run.  The suffix starts at `cuts.final.digest` and the
actual final oracle returned by `constructBoth`; it does not restart from an
independent empty state. -/
def runChronological {a b n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript -> Script Bytes Block Root a)
    (producerC2 : Oracle -> List Nat -> List Nat -> Script Bytes Block Root b)
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) :=
  continueRun tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2
    (fun cuts => authenticatedScript firstWork secondWork producer increment
      cuts body cuts.final.digest)

theorem success_decomposes {a b n m : Nat} (tape : Tape) (digest : Block)
    (producerC1 : Transcript -> Script Bytes Block Root a)
    (producerC2 : Oracle -> List Nat -> List Nat -> Script Bytes Block Root b)
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (cuts : RootCuts) (authenticated : Authenticated)
    (finalDigest : Block)
    (success : (runChronological tape digest producerC1 producerC2 firstWork
      secondWork producer increment body).1 =
        some (cuts, some (Except.ok authenticated, finalDigest))) :
    (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 =
        some cuts ∧
      (run tape (authenticatedScript firstWork secondWork producer increment
          cuts body cuts.final.digest) cuts.final.oracle).1 =
        some (Except.ok authenticated, finalDigest) ∧
      (runChronological tape digest producerC1 producerC2 firstWork secondWork
        producer increment body).2 =
        (run tape (authenticatedScript firstWork secondWork producer increment
          cuts body cuts.final.digest) cuts.final.oracle).2 := by
  cases early :
      (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).1 with
  | none => simp [runChronological, continueRun, early] at success
  | some produced =>
    have same : produced = cuts ∧
        (run tape (authenticatedScript firstWork secondWork producer increment
          produced body produced.final.digest)
          (constructBoth tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2).2.oracle).1 =
          some (Except.ok authenticated, finalDigest) := by
      simpa [runChronological, continueRun, early] using success
    have cutsEq : produced = cuts := same.1
    subst produced
    have stateEq := result_final tape ⟨digest, FSFirstFresh.empty⟩
      producerC1 producerC2 cuts early
    refine ⟨rfl, ?_, ?_⟩
    · simpa [stateEq] using same.2
    · simp [runChronological, continueRun, early, stateEq]

/-- Prefix answers, prefix inclusions and leaf/node inclusion are all produced
from the same successful chronological run. -/
theorem successful_authentication_inputs {a b n m : Nat}
    (tape : Tape) (digest : Block)
    (producerC1 : Transcript -> Script Bytes Block Root a)
    (producerC2 : Oracle -> List Nat -> List Nat -> Script Bytes Block Root b)
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (cuts : RootCuts) (authenticated : Authenticated)
    (finalDigest : Block)
    (success : (runChronological tape digest producerC1 producerC2 firstWork
      secondWork producer increment body).1 =
        some (cuts, some (Except.ok authenticated, finalDigest))) :
    let final := (runChronological tape digest producerC1 producerC2 firstWork
      secondWork producer increment body).2
    (∀ record ∈ oldRecords (c1Records cuts),
      oldView final record.1 = record.2) ∧
    (∀ record ∈ oldRecords (c2Records cuts),
      oldView final record.1 = record.2) ∧
    TraceIncludedInLog (rawPrefix (oldRecords (c1Records cuts))) (oldLog final) ∧
    TraceIncludedInLog (rawPrefix (oldRecords (c2Records cuts))) (oldLog final) ∧
    exists valid count,
      let positions := (liveSchedule authenticated.record.middle valid count).positions
      ∃ merkle : SuccessfulMerkleRun (oldView final) positions
          (encode authenticated.record.body),
        merkle.trace = authenticated.trace ∧
        merkle.wire.roots 0 = root208 cuts.c1 ∧
        merkle.wire.roots 1 = root208 cuts.c2 ∧
        TraceIncludedInLog
          (leafLog positions (wireRecords merkle.wire) ++ merkle.trace)
          (oldLog final) := by
  dsimp only
  obtain ⟨early, suffixSuccess, finalEq⟩ := success_decomposes tape digest
    producerC1 producerC2 firstWork secondWork producer increment body cuts
    authenticated finalDigest success
  have prefixFacts := chronological_old_prefixes tape digest producerC1 producerC2
    (fun cuts => authenticatedScript firstWork secondWork producer increment
      cuts body cuts.final.digest) cuts (some (.ok authenticated, finalDigest)) success
  rcases prefixFacts with ⟨answers1, answers2, included1, included2, _, _⟩
  have coherent := (constructBoth_valid_from_empty tape digest producerC1 producerC2).coherent
  rw [result_final tape ⟨digest, FSFirstFresh.empty⟩ producerC1 producerC2
    cuts early] at coherent
  obtain ⟨valid, count, merkle, traceEq, root0, root1, calls⟩ :=
    successful_constructs_merkle firstWork secondWork producer increment cuts body
      cuts.final.digest tape cuts.final.oracle authenticated finalDigest coherent suffixSuccess
  have answers1' : ∀ record ∈ oldRecords (c1Records cuts),
      oldView (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body cuts.final.digest) cuts.final.oracle).2 record.1 = record.2 := by
    rw [← finalEq]
    exact answers1
  have answers2' : ∀ record ∈ oldRecords (c2Records cuts),
      oldView (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body cuts.final.digest) cuts.final.oracle).2 record.1 = record.2 := by
    rw [← finalEq]
    exact answers2
  have included1' : TraceIncludedInLog
      (rawPrefix (oldRecords (c1Records cuts)))
      (oldLog (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body cuts.final.digest) cuts.final.oracle).2) := by
    rw [← finalEq]
    exact included1
  have included2' : TraceIncludedInLog
      (rawPrefix (oldRecords (c2Records cuts)))
      (oldLog (run tape (authenticatedScript firstWork secondWork producer increment
        cuts body cuts.final.digest) cuts.final.oracle).2) := by
    rw [← finalEq]
    exact included2
  rw [finalEq]
  exact ⟨answers1', answers2', included1', included2', valid, count, merkle,
    traceEq, root0, root1, calls⟩

/- DEFERRED TO A SMALLER FOLLOW-UP LEAF AFTER THE CONSTRUCTED AUTHENTICATION
INTERFACE ABOVE.  The first implementation attempt proved the Prepared/Merkle
wire and trace equalities but exhausted elaboration heartbeats at the final
large proposition equality; it is retained here as a commented diagnostic.

/-- The executable opening preparation is now attached to the source-built
prefixes and full opening log.  Preparation failure remains explicit.  On
success, authentication failure is retained as the existing alternative;
opening equality is obtained from the same-body theorem, not assumed. -/
def AuthenticatedScalarResult {view : RawHashInput -> Digest208}
    (prepared : Prepared view) (c1 c2 : AnswerPrefix)
    (fullLog : OrderedRawQueryLog) : Prop :=
  AuthenticationFailure view c1 c2 (wireRoots prepared.result.wire)
      fullLog prepared.query ∨
    prepared.scalar =
      ∑ i : Fin 22, prepared.rho^(i.val+1) *
        (AspisV8.SelectedReceivedOracle.oracle
          (0 : Fin 1024 -> SameBodyAuthenticatedIncrement.K)
          (AspisV8.SelectedQuotientOriginal.virtual prepared.data
            (prefixBatch c1 c2 prepared.result.wire prepared.data.gamma))).folded
              prepared.alpha
              (storedPoint (K := SameBodyAuthenticatedIncrement.K)
                (prepared.query i))

theorem prepare_authenticated_or_failure {a b n m : Nat}
    (tape : Tape) (digest : Block)
    (producerC1 : Transcript -> Script Bytes Block Root a)
    (producerC2 : Oracle -> List Nat -> List Nat -> Script Bytes Block Root b)
    (firstWork : Point -> Script Bytes Block Unit n)
    (secondWork : Point -> Point -> Script Bytes Block Unit m)
    (producer : FunctionalProducer) (increment : IncrementProducer)
    (body : Bytes) (cuts : RootCuts) (authenticated : Authenticated)
    (finalDigest : Block)
    (success : (runChronological tape digest producerC1 producerC2 firstWork
      secondWork producer increment body).1 =
        some (cuts, some (Except.ok authenticated, finalDigest)))
    (data : Data (K := SameBodyAuthenticatedIncrement.K)) :
    let final := (runChronological tape digest producerC1 producerC2 firstWork
      secondWork producer increment body).2
    (∃ valid count,
      SameBodyAuthenticatedIncrement.prepare (oldView final)
        authenticated.record.body
        (liveSchedule authenticated.record.middle valid count).positions data
        authenticated.record.middle.alpha0 authenticated.record.middle.rho =
          .error .openedPipeline) ∨
    ∃ valid count, ∃ prepared : Prepared (oldView final),
      SameBodyAuthenticatedIncrement.prepare (oldView final)
        authenticated.record.body
        (liveSchedule authenticated.record.middle valid count).positions data
        authenticated.record.middle.alpha0 authenticated.record.middle.rho =
          .ok prepared ∧
      AuthenticatedScalarResult prepared (oldRecords (c1Records cuts))
        (oldRecords (c2Records cuts)) (oldLog final) := by
  dsimp only
  obtain ⟨answers1, answers2, included1, included2, valid, count, merkle,
      _, _, _, calls⟩ := successful_authentication_inputs tape digest producerC1
    producerC2 firstWork secondWork producer increment body cuts authenticated
    finalDigest success
  let query := (liveSchedule authenticated.record.middle valid count).positions
  cases preparedEq : SameBodyAuthenticatedIncrement.prepare
      (oldView (runChronological tape digest producerC1 producerC2 firstWork
        secondWork producer increment body).2) authenticated.record.body query data
      authenticated.record.middle.alpha0 authenticated.record.middle.rho with
  | error e =>
    have errorExact : e = .openedPipeline := by cases e; rfl
    subst e
    exact Or.inl ⟨valid, count, preparedEq⟩
  | ok prepared =>
    apply Or.inr
    refine ⟨valid, count, prepared, preparedEq, ?_⟩
    have preparedFields :
        prepared.body = authenticated.record.body ∧
        prepared.query = query ∧ prepared.data = data ∧
        prepared.alpha = authenticated.record.middle.alpha0 ∧
        prepared.rho = authenticated.record.middle.rho := by
      unfold SameBodyAuthenticatedIncrement.prepare at preparedEq
      split at preparedEq
      · contradiction
      · cases preparedEq
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have preparedRun := prepared.runSuccess
    rw [preparedFields.1, preparedFields.2.1, preparedFields.2.2.1] at preparedRun
    have checks := AspisV8.SameBodyOpenedRun.run_checks (oldView
      (runChronological tape digest producerC1 producerC2 firstWork secondWork
        producer increment body).2) (wireBytes authenticated.record.body)
      query data prepared.result preparedRun
    have wireSame : prepared.result.wire = merkle.wire := by
      exact Option.some.inj (checks.1.symm.trans merkle.parsed)
    have traceSame : prepared.result.trace = merkle.trace := by
      have verified := checks.2.2.2
      rw [wireSame] at verified
      exact Option.some.inj (verified.symm.trans merkle.verified)
    have preparedCalls : TraceIncludedInLog
        (leafLog prepared.query (wireRecords prepared.result.wire) ++
          prepared.result.trace)
        (oldLog (runChronological tape digest producerC1 producerC2 firstWork
          secondWork producer increment body).2) := by
      have querySame : prepared.query = query := by
        unfold SameBodyAuthenticatedIncrement.prepare at preparedEq
        split at preparedEq
        · contradiction
        · cases preparedEq
          rfl
      rw [querySame, wireSame, traceSame]
      exact calls
    unfold AuthenticatedScalarResult
    exact authenticated_scalar_or_failure prepared
      (oldRecords (c1Records cuts)) (oldRecords (c2Records cuts))
      (oldLog (runChronological tape digest producerC1 producerC2 firstWork
        secondWork producer increment body).2)
      answers1 answers2 included1 included2 preparedCalls

-/

#print axioms success_decomposes
#print axioms successful_authentication_inputs

end
end AspisV8Completion.SameBodyChronologicalAuthentication
