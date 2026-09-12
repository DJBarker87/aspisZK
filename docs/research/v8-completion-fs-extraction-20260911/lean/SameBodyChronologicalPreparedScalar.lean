import SameBodyChronologicalAuthentication

/-!
# Chronological authentication to Prepared scalar

Small named equalities connect the source-constructed Merkle run to the
same-body `Prepared` opening pipeline before invoking the existing
authenticated-scalar theorem.  No prefix answer, inclusion, opening equality,
or preparation success is assumed globally: preparation failure remains an
explicit branch.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.SameBodyChronologicalPreparedScalar

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSQuerySchedule
open FSAuthenticationPrefixes FSV7PrefixBridge
open ExtractionCollectorAuthenticatedReplayable
open FSLiveSelectedMiddleQueryRho SameBodyLivePreparedIncrement
open SameBodyChronologicalAuthentication SameBodyAuthenticatedIncrement
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedMultiproofOpeningEquality AspisV8.SameBodyAuthenticatedSlots
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev RootCuts := FSBoundedTranscript.RootCuts
abbrev Point := FSV7OODBodyScript.Point
abbrev FunctionalProducer := FSLiveSelectedMiddleQueryRho.FunctionalProducer
abbrev IncrementProducer := FSLiveLaterRelationSuffix.IncrementProducer
abbrev K := SameBodyAuthenticatedIncrement.K
abbrev Position := AspisPool.V7MerkleQueryExtractor.Position

noncomputable section

theorem prepared_fields {view : RawHashInput -> Digest208}
    (body : Bytes) (query : Fin 22 -> Position) (data : Data (K := K))
    (alpha rho : K) (prepared : Prepared view)
    (success : SameBodyAuthenticatedIncrement.prepare view body query data alpha rho =
      .ok prepared) :
    prepared.body = body ∧ prepared.query = query ∧ prepared.data = data ∧
      prepared.alpha = alpha ∧ prepared.rho = rho := by
  unfold SameBodyAuthenticatedIncrement.prepare at success
  split at success
  · contradiction
  · cases success
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem prepared_wire_trace {view : RawHashInput -> Digest208}
    (body : Bytes) (query : Fin 22 -> Position) (data : Data (K := K))
    (alpha rho : K) (prepared : Prepared view)
    (success : SameBodyAuthenticatedIncrement.prepare view body query data alpha rho =
      .ok prepared) (merkle : SuccessfulMerkleRun view query (wireBytes body)) :
    prepared.result.wire = merkle.wire ∧ prepared.result.trace = merkle.trace := by
  have fields := prepared_fields body query data alpha rho prepared success
  have runSuccess := prepared.runSuccess
  rw [fields.1, fields.2.1, fields.2.2.1] at runSuccess
  have checks := AspisV8.SameBodyOpenedRun.run_checks view (wireBytes body)
    query data prepared.result runSuccess
  have wireSame : prepared.result.wire = merkle.wire :=
    Option.some.inj (checks.1.symm.trans merkle.parsed)
  have verified := checks.2.2.2
  rw [wireSame] at verified
  have traceSame : prepared.result.trace = merkle.trace :=
    Option.some.inj (verified.symm.trans merkle.verified)
  exact ⟨wireSame, traceSame⟩

theorem prepared_calls_included {view : RawHashInput -> Digest208}
    (body : Bytes) (query : Fin 22 -> Position) (data : Data (K := K))
    (alpha rho : K) (prepared : Prepared view)
    (success : SameBodyAuthenticatedIncrement.prepare view body query data alpha rho =
      .ok prepared) (merkle : SuccessfulMerkleRun view query (wireBytes body))
    (fullLog : OrderedRawQueryLog)
    (calls : TraceIncludedInLog
      (leafLog query (wireRecords merkle.wire) ++ merkle.trace) fullLog) :
    TraceIncludedInLog
      (leafLog prepared.query (wireRecords prepared.result.wire) ++
        prepared.result.trace) fullLog := by
  have fields := prepared_fields body query data alpha rho prepared success
  obtain ⟨wireSame, traceSame⟩ :=
    prepared_wire_trace body query data alpha rho prepared success merkle
  rw [fields.2.1, wireSame, traceSame]
  exact calls

structure ScalarOutcome {view : RawHashInput -> Digest208}
    (prepared : Prepared view) (c1 c2 : AnswerPrefix)
    (fullLog : OrderedRawQueryLog) : Prop where
  c1Answers : ∀ record ∈ c1, view record.1 = record.2
  c2Answers : ∀ record ∈ c2, view record.1 = record.2
  c1Included : TraceIncludedInLog (rawPrefix c1) fullLog
  c2Included : TraceIncludedInLog (rawPrefix c2) fullLog
  callsIncluded : TraceIncludedInLog
    (leafLog prepared.query (wireRecords prepared.result.wire) ++
      prepared.result.trace) fullLog

/-- The scalar alternative is not re-stated here: allowing Lean to infer the
result type avoids a second normalization of the large folded-oracle term. -/
noncomputable def ScalarOutcome.result {view : RawHashInput -> Digest208}
    {prepared : Prepared view} {c1 c2 : AnswerPrefix}
    {fullLog : OrderedRawQueryLog} (outcome : ScalarOutcome prepared c1 c2 fullLog) :=
  authenticated_scalar_or_failure prepared c1 c2 fullLog outcome.c1Answers
    outcome.c2Answers outcome.c1Included outcome.c2Included outcome.callsIncluded

inductive PreparationOutcome (view : RawHashInput -> Digest208) (body : Bytes)
    (middle : FSLiveSelectedMiddleQueryRho.Success) (data : Data (K := K))
    (valid : ValidAccepted middle.queries) (count : middle.queries.length = 22)
    (c1 c2 : AnswerPrefix) (fullLog : OrderedRawQueryLog) : Prop where
  | failed : SameBodyAuthenticatedIncrement.prepare view body
      (liveSchedule middle valid count).positions data middle.alpha0 middle.rho =
        .error .openedPipeline -> PreparationOutcome view body middle data valid count c1 c2 fullLog
  | authenticated (prepared : Prepared view) :
      SameBodyAuthenticatedIncrement.prepare view body
        (liveSchedule middle valid count).positions data middle.alpha0 middle.rho =
          .ok prepared ->
      ScalarOutcome prepared c1 c2 fullLog ->
      PreparationOutcome view body middle data valid count c1 c2 fullLog

theorem scalar_outcome_of_authenticated {view : RawHashInput -> Digest208}
    (prepared : Prepared view) (c1 c2 : AnswerPrefix)
    (fullLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2) fullLog)
    (callsIncluded : TraceIncludedInLog
      (leafLog prepared.query (wireRecords prepared.result.wire) ++
        prepared.result.trace) fullLog) :
    ScalarOutcome prepared c1 c2 fullLog :=
  ⟨c1Answers, c2Answers, c1Included, c2Included, callsIncluded⟩

structure ChronologicalPreparation (view : RawHashInput -> Digest208)
    (body : Bytes) (middle : FSLiveSelectedMiddleQueryRho.Success)
    (data : Data (K := K)) (c1 c2 : AnswerPrefix)
    (fullLog : OrderedRawQueryLog) : Prop where
  valid : ValidAccepted middle.queries
  count : middle.queries.length = 22
  outcome : PreparationOutcome view body middle data valid count c1 c2 fullLog

/-- The full deterministic composition.  Every authentication premise is an
output of `successful_authentication_inputs`; the only split is the actual
executable result of `prepare`. -/
theorem chronological_prepare_or_authenticated {a b n m : Nat}
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
    (data : Data (K := K)) :
    ChronologicalPreparation
      (oldView ((runChronological tape digest producerC1 producerC2 firstWork
        secondWork producer increment body).2))
      authenticated.record.body authenticated.record.middle data
      (oldRecords (c1Records cuts)) (oldRecords (c2Records cuts))
      (oldLog ((runChronological tape digest producerC1 producerC2 firstWork
        secondWork producer increment body).2)) := by
  obtain ⟨answers1, answers2, included1, included2, valid, count, merkle,
      _, _, _, calls⟩ := successful_authentication_inputs tape digest producerC1
    producerC2 firstWork secondWork producer increment body cuts authenticated
    finalDigest success
  let final := (runChronological tape digest producerC1 producerC2 firstWork
    secondWork producer increment body).2
  let query := (liveSchedule authenticated.record.middle valid count).positions
  cases preparedEq : SameBodyAuthenticatedIncrement.prepare (oldView final)
      authenticated.record.body query data authenticated.record.middle.alpha0
      authenticated.record.middle.rho with
  | error e =>
    have errorExact : e = .openedPipeline := by cases e; rfl
    subst e
    exact ⟨valid, count, PreparationOutcome.failed (by
      simpa [final, query] using preparedEq)⟩
  | ok prepared =>
    have callFacts := prepared_calls_included authenticated.record.body query data
      authenticated.record.middle.alpha0 authenticated.record.middle.rho prepared
      preparedEq merkle (oldLog final) calls
    exact ⟨valid, count, PreparationOutcome.authenticated prepared (by
      simpa [final, query] using preparedEq) (scalar_outcome_of_authenticated
        prepared (oldRecords (c1Records cuts)) (oldRecords (c2Records cuts))
        (oldLog final) answers1 answers2 included1 included2 callFacts)⟩

#print axioms prepared_fields
#print axioms prepared_wire_trace
#print axioms prepared_calls_included
#print axioms scalar_outcome_of_authenticated
#print axioms ScalarOutcome.result
#print axioms chronological_prepare_or_authenticated

end
end AspisV8Completion.SameBodyChronologicalPreparedScalar
